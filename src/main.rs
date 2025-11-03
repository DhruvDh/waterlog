mod rower_nom;

use std::{fmt::Write as FmtWrite, time::Duration};

use anyhow::{Context, Result, bail};
use bpaf::{OptionParser, Parser, construct, long, pure};
use btleplug::{
    api::{
        Central, CharPropFlags, Characteristic, Manager as _, Peripheral as _, ScanFilter,
        ValueNotification, WriteType,
    },
    platform::{Adapter, Manager, Peripheral},
};
use futures::StreamExt;
use tokio::time;
use tracing::{Level, debug, info, warn};
use uuid::Uuid;

const FTMS_SVC: Uuid = Uuid::from_u128(0x0000_1826_0000_1000_8000_0080_5F9B_34FB);
const ROWER_DATA_CH: Uuid = Uuid::from_u128(0x0000_2AD1_0000_1000_8000_0080_5F9B_34FB);
const CTRL_POINT_CH: Uuid = Uuid::from_u128(0x0000_2AD9_0000_1000_8000_0080_5F9B_34FB);
const STATUS_CH: Uuid = Uuid::from_u128(0x0000_2ADA_0000_1000_8000_0080_5F9B_34FB);

#[derive(Debug, Clone)]
enum Command {
    List,
    Stream { handshake: bool },
}

fn list_command() -> impl Parser<Command> {
    pure(Command::List)
        .to_options()
        .descr("Scan, connect, and print all advertised services and characteristics")
        .command("list")
}

fn stream_command() -> impl Parser<Command> {
    let handshake = long("handshake")
        .help("Issue FTMS Request Control and Start/Resume before listening")
        .switch();
    construct!(Command::Stream { handshake })
        .to_options()
        .descr("Subscribe to the FTMS Rower Data characteristic")
        .command("stream")
}

fn cli() -> OptionParser<Command> {
    construct!([list_command(), stream_command()])
        .to_options()
        .descr("MERACH/FTMS probe in Rust")
        .version(env!("CARGO_PKG_VERSION"))
}

#[tokio::main]
async fn main() -> Result<()> {
    tracing_subscriber::fmt()
        .with_max_level(Level::INFO)
        .compact()
        .init();

    let cmd = cli().run();

    let adapter = init_adapter().await?;

    match cmd {
        Command::List => list_gatt(&adapter).await?,
        Command::Stream { handshake } => stream_rower(&adapter, handshake).await?,
    }

    Ok(())
}

async fn list_gatt(adapter: &Adapter) -> Result<()> {
    let peripheral = connect_target(adapter).await?;

    if let Some(props) = peripheral.properties().await? {
        info!(?props, "Connected to peripheral");
    } else {
        warn!("Connected, but peripheral properties were unavailable");
    }

    for ch in peripheral.characteristics() {
        let props = fmt_props(ch.properties);
        info!(
            service = %ch.service_uuid,
            characteristic = %ch.uuid,
            properties = %props,
            "Characteristic discovered"
        );
    }

    Ok(())
}

async fn stream_rower(adapter: &Adapter, handshake: bool) -> Result<()> {
    let peripheral = connect_target(adapter).await?;
    let characteristics = find_rower_characteristics(&peripheral)?;

    peripheral
        .subscribe(&characteristics.data)
        .await
        .context("Failed to subscribe to Rower Data notifications")?;

    if handshake {
        perform_handshake(&peripheral, &characteristics).await?;
    }

    let mut notifications = peripheral.notifications().await?;
    let mut assembler = rower_nom::RowerAssembler::default();
    let mut last_record: Option<rower_nom::RowerRecord> = None;
    info!("Waiting for Rower Data notifications...");

    while let Some(notification) = notifications.next().await {
        match classify_notification(&notification, &characteristics) {
            NotificationKind::RowerData => {
                match rower_nom::parse_rower_fragment(&notification.value) {
                    Ok((remaining, fragment)) => {
                        let flags = fragment.flags;
                        if !remaining.is_empty() {
                            warn!(
                                flags = %format_args!("0x{flags:04X}"),
                                trailing = %hex(remaining),
                                "Trailing bytes after FTMS parse"
                            );
                        }
                        if let Some(mut record) = assembler.push(fragment) {
                            enhance_instant_pace(&mut record, last_record.as_ref());
                            info!("{record}");
                            last_record = Some(record);
                        }
                    }
                    Err(err) => {
                        warn!(
                            error = ?err,
                            raw = %hex(&notification.value),
                            "Failed to parse FTMS rower data"
                        );
                    }
                }
            }
            NotificationKind::ControlPoint => {
                info!(response = %hex(&notification.value), "Control Point response");
            }
            NotificationKind::Status => {
                info!(payload = %hex(&notification.value), "Status notification");
            }
            NotificationKind::Other => {
                debug!(
                    uuid = %notification.uuid,
                    payload = %hex(&notification.value),
                    "Unhandled notification"
                );
            }
        }
    }

    Ok(())
}

fn enhance_instant_pace(
    current: &mut rower_nom::RowerRecord,
    previous: Option<&rower_nom::RowerRecord>,
) {
    let ok = current
        .inst_pace_s_per_500m
        .map(|pace| pace != 0)
        .unwrap_or(false);
    if ok {
        return;
    }

    let Some(prev) = previous else {
        return;
    };

    let (Some(d2), Some(d1), Some(t2), Some(t1)) = (
        current.total_distance_m,
        prev.total_distance_m,
        current.elapsed_time_s,
        prev.elapsed_time_s,
    ) else {
        return;
    };

    let dd = d2.saturating_sub(d1);
    let dt = t2.saturating_sub(t1);
    if dd == 0 || dt == 0 {
        return;
    }

    let pace = (500u32 * dt as u32) / dd as u32;
    current.inst_pace_s_per_500m = Some(pace as u16);
}

async fn init_adapter() -> Result<Adapter> {
    let manager = Manager::new()
        .await
        .context("Bluetooth adapter manager initialisation failed")?;
    let adapters = manager.adapters().await?;
    adapters
        .into_iter()
        .next()
        .context("No Bluetooth adapters found")
}

async fn connect_target(adapter: &Adapter) -> Result<Peripheral> {
    let peripheral = pick_ftms_device(adapter).await?;
    connect_and_discover(&peripheral).await?;
    Ok(peripheral)
}

async fn pick_ftms_device(adapter: &Adapter) -> Result<Peripheral> {
    adapter
        .start_scan(ScanFilter::default())
        .await
        .context("Failed to start BLE scan")?;
    // Give the adapter a moment to populate devices.
    time::sleep(Duration::from_secs(3)).await;

    let mut candidate = None;
    for peripheral in adapter.peripherals().await? {
        let Some(props) = peripheral.properties().await? else {
            continue;
        };

        if props.services.contains(&FTMS_SVC) {
            candidate = Some(peripheral);
            break;
        }
    }

    adapter
        .stop_scan()
        .await
        .context("Failed to stop BLE scan")?;

    if let Some(peripheral) = candidate {
        Ok(peripheral)
    } else {
        bail!("No FTMS-like device found (make sure the console is awake)");
    }
}

async fn connect_and_discover(peripheral: &Peripheral) -> Result<()> {
    if !peripheral.is_connected().await? {
        peripheral
            .connect()
            .await
            .context("Failed to connect to peripheral")?;
    }

    peripheral
        .discover_services()
        .await
        .context("Service discovery failed")?;
    Ok(())
}

struct RowerCharacteristics {
    data: Characteristic,
    ctrl_point: Option<Characteristic>,
    status: Option<Characteristic>,
}

fn find_rower_characteristics(peripheral: &Peripheral) -> Result<RowerCharacteristics> {
    let mut data = None;
    let mut ctrl_point = None;
    let mut status = None;

    for ch in peripheral.characteristics() {
        if ch.uuid == ROWER_DATA_CH {
            data = Some(ch.clone());
        } else if ch.uuid == CTRL_POINT_CH {
            ctrl_point = Some(ch.clone());
        } else if ch.uuid == STATUS_CH {
            status = Some(ch.clone());
        }
    }

    let data = data.context("Rower Data (0x2AD1) characteristic not found")?;
    Ok(RowerCharacteristics {
        data,
        ctrl_point,
        status,
    })
}

async fn perform_handshake(peripheral: &Peripheral, chars: &RowerCharacteristics) -> Result<()> {
    if let Some(ctrl) = &chars.ctrl_point {
        peripheral
            .subscribe(ctrl)
            .await
            .context("Failed to subscribe to Control Point indications")?;

        peripheral
            .write(ctrl, &[0x00], WriteType::WithResponse)
            .await
            .context("Control Point Request Control (0x00) failed")?;
        peripheral
            .write(ctrl, &[0x07], WriteType::WithResponse)
            .await
            .context("Control Point Start/Resume (0x07) failed")?;
        info!("Sent FTMS Request Control + Start/Resume");
    } else {
        warn!("Control Point (0x2AD9) missing; skipping handshake");
    }

    if let Some(status) = &chars.status {
        if let Err(err) = peripheral.subscribe(status).await {
            warn!(error = ?err, "Failed to subscribe to Rower Status indications");
        }
    }

    Ok(())
}

fn fmt_props(props: CharPropFlags) -> String {
    let labels = [
        (CharPropFlags::READ, "READ"),
        (CharPropFlags::WRITE, "WRITE"),
        (CharPropFlags::WRITE_WITHOUT_RESPONSE, "WRITE_NR"),
        (CharPropFlags::NOTIFY, "NOTIFY"),
        (CharPropFlags::INDICATE, "INDICATE"),
    ];

    let mut first = true;
    let mut s = String::new();
    for (flag, label) in labels {
        if props.contains(flag) {
            if !first {
                s.push(' ');
            }
            first = false;
            s.push_str(label);
        }
    }
    s
}

fn hex(bytes: &[u8]) -> String {
    let mut s = String::new();
    for (idx, byte) in bytes.iter().enumerate() {
        if idx > 0 {
            let _ = write!(s, " ");
        }
        let _ = write!(s, "{:02X}", byte);
    }
    s
}

enum NotificationKind {
    RowerData,
    ControlPoint,
    Status,
    Other,
}

fn classify_notification(
    notification: &ValueNotification,
    chars: &RowerCharacteristics,
) -> NotificationKind {
    if notification.uuid == chars.data.uuid {
        NotificationKind::RowerData
    } else if chars
        .ctrl_point
        .as_ref()
        .map(|ch| ch.uuid == notification.uuid)
        .unwrap_or(false)
    {
        NotificationKind::ControlPoint
    } else if chars
        .status
        .as_ref()
        .map(|ch| ch.uuid == notification.uuid)
        .unwrap_or(false)
    {
        NotificationKind::Status
    } else {
        NotificationKind::Other
    }
}
