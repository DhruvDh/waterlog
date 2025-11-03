use anyhow::{Context, Result, bail};
use bpaf::{OptionParser, Parser, construct, long};
use btleplug::api::{Central, CharPropFlags, Manager as _, Peripheral as _, ScanFilter, WriteType};
use btleplug::platform::{Adapter, Manager, Peripheral};
use futures::StreamExt;
use std::{fmt::Write as FmtWrite, time::Duration};
use tokio::time;
use tracing::Level;
use uuid::Uuid;

const FTMS_SVC: Uuid = Uuid::from_u128(0x0000_1826_0000_1000_8000_0080_5F9B_34FB);
const ROWER_DATA_CH: Uuid = Uuid::from_u128(0x0000_2AD1_0000_1000_8000_0080_5F9B_34FB);
const CTRL_POINT_CH: Uuid = Uuid::from_u128(0x0000_2AD9_0000_1000_8000_0080_5F9B_34FB);
const STATUS_CH: Uuid = Uuid::from_u128(0x0000_2ADA_0000_1000_8000_0080_5F9B_34FB);

#[derive(Debug, Clone)]
struct ListOptions {
    name_contains: Option<String>,
}

#[derive(Debug, Clone)]
struct StreamOptions {
    handshake: bool,
    name_contains: Option<String>,
}

#[derive(Debug, Clone)]
enum Command {
    List(ListOptions),
    Stream(StreamOptions),
}

fn list_args() -> impl Parser<ListOptions> {
    let name_contains = long("name-contains")
        .help("Filter target peripherals by case-sensitive substring match on the name")
        .argument::<String>("SUBSTRING")
        .optional();
    construct!(ListOptions { name_contains })
}

fn stream_args() -> impl Parser<StreamOptions> {
    let handshake = long("handshake")
        .help("Issue FTMS Request Control and Start/Resume before listening")
        .switch();
    let name_contains = long("name-contains")
        .help("Filter target peripherals by case-sensitive substring match on the name")
        .argument::<String>("SUBSTRING")
        .optional();
    construct!(StreamOptions {
        handshake,
        name_contains
    })
}

fn cli() -> OptionParser<Command> {
    let list = list_args()
        .to_options()
        .descr("Scan, connect, and print all advertised services and characteristics")
        .command("list")
        .map(Command::List);

    let stream = stream_args()
        .to_options()
        .descr("Subscribe to the FTMS Rower Data characteristic")
        .command("stream")
        .map(Command::Stream);

    construct!([list, stream])
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

    let manager = Manager::new()
        .await
        .context("Bluetooth adapter manager initialisation failed")?;
    let adapters = manager.adapters().await?;
    let Some(adapter) = adapters.into_iter().next() else {
        bail!("No Bluetooth adapters found");
    };

    match cmd {
        Command::List(opts) => list_gatt(&adapter, opts.name_contains.as_deref()).await?,
        Command::Stream(opts) => {
            stream_rower(&adapter, opts.name_contains.as_deref(), opts.handshake).await?
        }
    }

    Ok(())
}

async fn list_gatt(adapter: &Adapter, name_contains: Option<&str>) -> Result<()> {
    let peripheral = pick_ftms_device(adapter, name_contains).await?;
    connect_and_discover(&peripheral).await?;

    if let Some(props) = peripheral.properties().await? {
        println!("Connected to: {:?}", props);
    } else {
        println!("Connected, but peripheral properties were unavailable");
    }

    for ch in peripheral.characteristics() {
        println!(
            "- svc={} ch={} props=[{}]",
            ch.service_uuid,
            ch.uuid,
            fmt_props(ch.properties)
        );
    }

    Ok(())
}

async fn stream_rower(
    adapter: &Adapter,
    name_contains: Option<&str>,
    handshake: bool,
) -> Result<()> {
    let peripheral = pick_ftms_device(adapter, name_contains).await?;
    connect_and_discover(&peripheral).await?;

    let mut rower_data = None;
    let mut ctrl_point = None;
    let mut status = None;

    for ch in peripheral.characteristics() {
        if ch.uuid == ROWER_DATA_CH {
            rower_data = Some(ch.clone());
        } else if ch.uuid == CTRL_POINT_CH {
            ctrl_point = Some(ch.clone());
        } else if ch.uuid == STATUS_CH {
            status = Some(ch.clone());
        }
    }

    let rower = rower_data.context("Rower Data (0x2AD1) characteristic not found")?;

    peripheral
        .subscribe(&rower)
        .await
        .context("Failed to subscribe to Rower Data notifications")?;

    if handshake {
        if let Some(cp) = &ctrl_point {
            peripheral
                .subscribe(cp)
                .await
                .context("Failed to subscribe to Control Point indications")?;

            peripheral
                .write(cp, &[0x00], WriteType::WithResponse)
                .await
                .context("Control Point Request Control (0x00) failed")?;
            peripheral
                .write(cp, &[0x07], WriteType::WithResponse)
                .await
                .context("Control Point Start/Resume (0x07) failed")?;
            println!("Sent FTMS Request Control + Start/Resume");
        } else {
            println!("Control Point (0x2AD9) missing; skipping handshake");
        }

        if let Some(status) = &status {
            let _ = peripheral.subscribe(status).await;
        }
    }

    let ctrl_uuid = ctrl_point.as_ref().map(|c| c.uuid);
    let status_uuid = status.as_ref().map(|c| c.uuid);

    let mut notifications = peripheral.notifications().await?;
    println!("Waiting for Rower Data notifications...");

    while let Some(notification) = notifications.next().await {
        if notification.uuid == rower.uuid {
            println!("rower 0x2AD1: {}", hex(&notification.value));
            if let Some((spm, strokes)) = try_parse_minimal_rower(&notification.value) {
                println!("  spm={} stroke_count={}", spm, strokes);
            }
        } else if Some(notification.uuid) == ctrl_uuid {
            println!("ctrl-point resp: {}", hex(&notification.value));
        } else if Some(notification.uuid) == status_uuid {
            println!("status: {}", hex(&notification.value));
        }
    }

    Ok(())
}

async fn pick_ftms_device(adapter: &Adapter, name_contains: Option<&str>) -> Result<Peripheral> {
    adapter
        .start_scan(ScanFilter::default())
        .await
        .context("Failed to start BLE scan")?;
    // Give the adapter a moment to populate devices.
    time::sleep(Duration::from_secs(3)).await;

    let mut candidates = Vec::new();
    for peripheral in adapter.peripherals().await? {
        let Some(props) = peripheral.properties().await? else {
            continue;
        };

        let name = props.local_name.unwrap_or_default();
        let name_ok = name_contains
            .map(|needle| name.contains(needle))
            .unwrap_or(true);
        let svc_ok = props.services.iter().any(|svc| *svc == FTMS_SVC);

        if name_ok && svc_ok {
            candidates.push(peripheral);
        }
    }

    candidates
        .into_iter()
        .next()
        .context("No FTMS-like device found (try --name-contains or wake the console)")
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

fn fmt_props(props: CharPropFlags) -> String {
    let mut s = String::new();
    if props.contains(CharPropFlags::READ) {
        let _ = write!(s, "READ ");
    }
    if props.contains(CharPropFlags::WRITE) {
        let _ = write!(s, "WRITE ");
    }
    if props.contains(CharPropFlags::WRITE_WITHOUT_RESPONSE) {
        let _ = write!(s, "WRITE_NR ");
    }
    if props.contains(CharPropFlags::NOTIFY) {
        let _ = write!(s, "NOTIFY ");
    }
    if props.contains(CharPropFlags::INDICATE) {
        let _ = write!(s, "INDICATE ");
    }
    s.trim_end().to_owned()
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

fn try_parse_minimal_rower(bytes: &[u8]) -> Option<(u16, u16)> {
    if bytes.len() < 6 {
        return None;
    }
    let _flags = u16::from_le_bytes([bytes[0], bytes[1]]);
    let spm = u16::from_le_bytes([bytes[2], bytes[3]]);
    let strokes = u16::from_le_bytes([bytes[4], bytes[5]]);
    if spm == 0 || spm > 120 {
        return None;
    }
    Some((spm, strokes))
}
