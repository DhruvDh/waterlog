use nom::{
    IResult, Parser,
    bytes::complete::take,
    combinator::cond,
    error::context,
    number::complete::{le_i16, le_u16, u8 as parse_u8},
};
use nom_language::error::VerboseError;

pub type PResult<'a, T> = IResult<&'a [u8], T, VerboseError<&'a [u8]>>;

#[derive(Debug, Clone, Default)]
pub struct RowerFragment {
    pub flags: u16,
    pub more_data: bool,
    pub stroke_rate_half_spm: Option<u8>,
    pub stroke_count: Option<u16>,
    pub avg_stroke_rate_half_spm: Option<u8>,
    pub total_distance_m: Option<u32>,
    pub inst_pace_s_per_500m: Option<u16>,
    pub avg_pace_s_per_500m: Option<u16>,
    pub inst_power_w: Option<i16>,
    pub avg_power_w: Option<i16>,
    pub resistance_level: Option<u8>,
    pub total_energy_kcal: Option<u16>,
    pub energy_per_hour_kcal: Option<u16>,
    pub energy_per_minute_kcal: Option<u8>,
    pub heart_rate_bpm: Option<u8>,
    pub metabolic_equiv_tenths: Option<u8>,
    pub elapsed_time_s: Option<u16>,
    pub remaining_time_s: Option<u16>,
}

#[derive(Debug, Clone, Default)]
pub struct RowerRecord {
    pub flags: u16,
    pub stroke_rate_half_spm: Option<u8>,
    pub stroke_count: Option<u16>,
    pub avg_stroke_rate_half_spm: Option<u8>,
    pub total_distance_m: Option<u32>,
    pub inst_pace_s_per_500m: Option<u16>,
    pub avg_pace_s_per_500m: Option<u16>,
    pub inst_power_w: Option<i16>,
    pub avg_power_w: Option<i16>,
    pub resistance_level: Option<u8>,
    pub total_energy_kcal: Option<u16>,
    pub energy_per_hour_kcal: Option<u16>,
    pub energy_per_minute_kcal: Option<u8>,
    pub heart_rate_bpm: Option<u8>,
    pub metabolic_equiv_tenths: Option<u8>,
    pub elapsed_time_s: Option<u16>,
    pub remaining_time_s: Option<u16>,
}

impl RowerRecord {
    fn absorb(&mut self, fragment: &RowerFragment) {
        self.flags |= fragment.flags & !1;
        macro_rules! set_if_some {
            ($field:ident) => {
                if fragment.$field.is_some() {
                    self.$field = fragment.$field;
                }
            };
        }

        set_if_some!(stroke_rate_half_spm);
        set_if_some!(stroke_count);
        set_if_some!(avg_stroke_rate_half_spm);
        set_if_some!(total_distance_m);
        set_if_some!(inst_pace_s_per_500m);
        set_if_some!(avg_pace_s_per_500m);
        set_if_some!(inst_power_w);
        set_if_some!(avg_power_w);
        set_if_some!(resistance_level);
        set_if_some!(total_energy_kcal);
        set_if_some!(energy_per_hour_kcal);
        set_if_some!(energy_per_minute_kcal);
        set_if_some!(heart_rate_bpm);
        set_if_some!(metabolic_equiv_tenths);
        set_if_some!(elapsed_time_s);
        set_if_some!(remaining_time_s);
    }

    pub fn stroke_rate_spm(&self) -> Option<f32> {
        self.stroke_rate_half_spm.map(|half| half as f32 / 2.0)
    }

    pub fn avg_stroke_rate_spm(&self) -> Option<f32> {
        self.avg_stroke_rate_half_spm.map(|half| half as f32 / 2.0)
    }

    pub fn metabolic_equiv(&self) -> Option<f32> {
        self.metabolic_equiv_tenths
            .map(|tenths| tenths as f32 / 10.0)
    }
}

#[derive(Default)]
pub struct RowerAssembler {
    current: RowerRecord,
}

impl RowerAssembler {
    pub fn push(&mut self, fragment: RowerFragment) -> Option<RowerRecord> {
        self.current.absorb(&fragment);
        if fragment.more_data {
            None
        } else {
            let record = std::mem::take(&mut self.current);
            Some(record)
        }
    }
}

#[inline]
fn bit(flags: u16, idx: u8) -> bool {
    (flags & (1 << idx)) != 0
}

#[inline]
fn none_if_eq<T>(value: T, sentinel: T) -> Option<T>
where
    T: PartialEq,
{
    if value == sentinel { None } else { Some(value) }
}

fn parse_u24(input: &[u8]) -> PResult<'_, u32> {
    let (i, bytes) = take(3usize)(input)?;
    let value = (bytes[0] as u32) | ((bytes[1] as u32) << 8) | ((bytes[2] as u32) << 16);
    Ok((i, value))
}

pub fn parse_rower_fragment(input: &[u8]) -> PResult<'_, RowerFragment> {
    context("rower_data", |i| {
        let (i, flags) = context("flags", le_u16).parse(i)?;
        let more = bit(flags, 0);

        let (i, sr_raw) = context("stroke_rate_half_spm", parse_u8).parse(i)?;
        let (i, sc_raw) = context("stroke_count", le_u16).parse(i)?;
        let stroke_rate_half_spm = if more { None } else { Some(sr_raw) };
        let stroke_count = if more { None } else { Some(sc_raw) };

        let (i, avg_stroke_rate_half_spm) = cond(bit(flags, 1), parse_u8).parse(i)?;
        let (i, total_distance_m) = cond(bit(flags, 2), |i| {
            context("total_distance_m", parse_u24).parse(i)
        })
        .parse(i)?;
        let (i, inst_pace_s_per_500m) = cond(bit(flags, 3), le_u16).parse(i)?;
        let (i, avg_pace_s_per_500m) = cond(bit(flags, 4), le_u16).parse(i)?;
        let (i, inst_power_w) = cond(bit(flags, 5), le_i16).parse(i)?;
        let (i, avg_power_w) = cond(bit(flags, 6), le_i16).parse(i)?;
        let (i, resistance_level) = cond(bit(flags, 7), parse_u8).parse(i)?;

        let (i, energy_group) = cond(bit(flags, 8), |i| {
            let (i, total) = context("energy.total_kcal", le_u16).parse(i)?;
            let (i, per_hour) = context("energy.per_hour_kcal", le_u16).parse(i)?;
            let (i, per_minute) = context("energy.per_min_kcal", parse_u8).parse(i)?;
            Ok((i, (total, per_hour, per_minute)))
        })
        .parse(i)?;

        let (i, heart_rate_bpm) = cond(bit(flags, 9), parse_u8).parse(i)?;
        let (i, metabolic_equiv_tenths) = cond(bit(flags, 10), parse_u8).parse(i)?;
        let (i, elapsed_time_s) = cond(bit(flags, 11), le_u16).parse(i)?;
        let (i, remaining_time_s) = cond(bit(flags, 12), le_u16).parse(i)?;

        let (total_energy_kcal, energy_per_hour_kcal, energy_per_minute_kcal) = match energy_group {
            Some((total, per_hour, per_minute)) => (
                none_if_eq(total, 0xFFFF),
                none_if_eq(per_hour, 0xFFFF),
                none_if_eq(per_minute, 0xFF),
            ),
            None => (None, None, None),
        };

        let fragment = RowerFragment {
            flags,
            more_data: more,
            stroke_rate_half_spm,
            stroke_count,
            avg_stroke_rate_half_spm,
            total_distance_m,
            inst_pace_s_per_500m,
            avg_pace_s_per_500m,
            inst_power_w,
            avg_power_w,
            resistance_level,
            total_energy_kcal,
            energy_per_hour_kcal,
            energy_per_minute_kcal,
            heart_rate_bpm,
            metabolic_equiv_tenths,
            elapsed_time_s,
            remaining_time_s,
        };

        Ok((i, fragment))
    })
    .parse(input)
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn parses_simple_final_fragment() {
        let bytes: [u8; 14] = [
            0x00, 0x0F, // flags (bits 8, 9, 10, 11 set; MoreData=0)
            0x2A, // stroke rate half-spm
            0x11, 0x00, // stroke count
            0xFF, 0xFF, // total energy sentinel
            0xFF, 0xFF, // energy/hour sentinel
            0xFF, // energy/min sentinel
            0x60, // heart rate
            0x19, // MET*10
            0x34, 0x12, // elapsed time
        ];

        let (rem, fragment) = parse_rower_fragment(&bytes).expect("parse");
        assert!(rem.is_empty());
        assert!(!fragment.more_data);
        assert_eq!(fragment.stroke_rate_half_spm, Some(42));
        assert_eq!(fragment.stroke_count, Some(17));
        assert_eq!(fragment.total_energy_kcal, None);
        assert_eq!(fragment.energy_per_hour_kcal, None);
        assert_eq!(fragment.energy_per_minute_kcal, None);
        assert_eq!(fragment.heart_rate_bpm, Some(96));
        assert_eq!(fragment.metabolic_equiv_tenths, Some(25));
        assert_eq!(fragment.elapsed_time_s, Some(0x1234));
    }

    #[test]
    fn assembler_emits_on_final_fragment() {
        let mut assembler = RowerAssembler::default();

        let mut first = RowerFragment::default();
        first.flags = 0x0041; // MoreData + Avg Power Present
        first.more_data = true;
        first.avg_power_w = Some(150);
        assert!(assembler.push(first).is_none());

        let mut second = RowerFragment::default();
        second.flags = 0x0000;
        second.more_data = false;
        second.stroke_rate_half_spm = Some(40);
        second.stroke_count = Some(100);

        let record = assembler.push(second).expect("record");
        assert_eq!(record.stroke_rate_half_spm, Some(40));
        assert_eq!(record.stroke_count, Some(100));
        assert_eq!(record.avg_power_w, Some(150));
        assert_eq!(record.flags, 0x0040);
    }

    #[test]
    fn parses_intermediate_fragment_without_base_fields() {
        // MoreData = 1, Average Power present (bit 6)
        let bytes: [u8; 7] = [
            0x41, 0x00, // flags (MoreData=1, bit6 set)
            0x00, // stroke rate placeholder (should be ignored)
            0x00, 0x00, // stroke count placeholder (ignored)
            0x96, 0x00, // avg power = 150 W
        ];

        let (rem, fragment) = parse_rower_fragment(&bytes).expect("parse");
        assert!(rem.is_empty());
        assert!(fragment.more_data);
        assert_eq!(fragment.stroke_rate_half_spm, None);
        assert_eq!(fragment.stroke_count, None);
        assert_eq!(fragment.avg_power_w, Some(150));
    }

    #[test]
    fn parses_energy_group_in_lockstep() {
        let bytes: [u8; 10] = [
            0x00, 0x01, // flags (bit0=0, bit8 set)
            0x20, // stroke rate half-spm (MoreData=0 so recorded)
            0x05, 0x00, // stroke count
            0x10, 0x27, // total energy 10000 kcal -> sentinel? (not sentinel)
            0xFF, 0xFF, // energy per hour sentinel -> None
            0x32, // energy per minute 50 kcal
        ];

        let (rem, fragment) = parse_rower_fragment(&bytes).expect("parse");
        assert!(rem.is_empty());
        assert_eq!(fragment.total_energy_kcal, Some(0x2710));
        assert_eq!(fragment.energy_per_hour_kcal, None);
        assert_eq!(fragment.energy_per_minute_kcal, Some(50));
    }
}

#[cfg(test)]
mod prop_tests {
    use super::*;
    use proptest::prelude::*;
    use proptest::prop_compose;
    use proptest::test_runner::TestCaseError;

    #[allow(clippy::too_many_arguments)]
    fn build_fragment(
        more_data: bool,
        f_avg_spm: bool,
        f_dist: bool,
        f_inst_pace: bool,
        f_avg_pace: bool,
        f_inst_power: bool,
        f_avg_power: bool,
        f_resist: bool,
        f_energy: bool,
        f_hr: bool,
        f_met: bool,
        f_elapsed: bool,
        f_remaining: bool,
        sr_half: u8,
        stroke_count: u16,
        avg_spm_val: u8,
        dist_raw: u32,
        inst_pace_val: u16,
        avg_pace_val: u16,
        inst_power_val: i16,
        avg_power_val: i16,
        resist_val: u8,
        energy_total_val: u16,
        energy_hour_val: u16,
        energy_min_val: u8,
        hr_val: u8,
        met_val: u8,
        elapsed_val: u16,
        remaining_val: u16,
    ) -> (Vec<u8>, RowerFragment) {
        let mut flags: u16 = 0;
        if more_data {
            flags |= 1 << 0;
        }
        if f_avg_spm {
            flags |= 1 << 1;
        }
        if f_dist {
            flags |= 1 << 2;
        }
        if f_inst_pace {
            flags |= 1 << 3;
        }
        if f_avg_pace {
            flags |= 1 << 4;
        }
        if f_inst_power {
            flags |= 1 << 5;
        }
        if f_avg_power {
            flags |= 1 << 6;
        }
        if f_resist {
            flags |= 1 << 7;
        }
        if f_energy {
            flags |= 1 << 8;
        }
        if f_hr {
            flags |= 1 << 9;
        }
        if f_met {
            flags |= 1 << 10;
        }
        if f_elapsed {
            flags |= 1 << 11;
        }
        if f_remaining {
            flags |= 1 << 12;
        }

        let mut bytes = vec![(flags & 0x00FF) as u8, (flags >> 8) as u8];

        bytes.push(sr_half);
        bytes.extend_from_slice(&stroke_count.to_le_bytes());

        let stroke_rate_half_spm = if more_data { None } else { Some(sr_half) };
        let stroke_count_opt = if more_data { None } else { Some(stroke_count) };

        let mut avg_spm_opt = None;
        if f_avg_spm {
            bytes.push(avg_spm_val);
            avg_spm_opt = Some(avg_spm_val);
        }

        let mut dist_opt = None;
        if f_dist {
            let d = dist_raw & 0x00FF_FFFF;
            bytes.push((d & 0xFF) as u8);
            bytes.push(((d >> 8) & 0xFF) as u8);
            bytes.push(((d >> 16) & 0xFF) as u8);
            dist_opt = Some(d);
        }

        let mut inst_pace_opt = None;
        if f_inst_pace {
            bytes.extend_from_slice(&inst_pace_val.to_le_bytes());
            inst_pace_opt = Some(inst_pace_val);
        }

        let mut avg_pace_opt = None;
        if f_avg_pace {
            bytes.extend_from_slice(&avg_pace_val.to_le_bytes());
            avg_pace_opt = Some(avg_pace_val);
        }

        let mut inst_power_opt = None;
        if f_inst_power {
            bytes.extend_from_slice(&inst_power_val.to_le_bytes());
            inst_power_opt = Some(inst_power_val);
        }

        let mut avg_power_opt = None;
        if f_avg_power {
            bytes.extend_from_slice(&avg_power_val.to_le_bytes());
            avg_power_opt = Some(avg_power_val);
        }

        let mut resist_opt = None;
        if f_resist {
            bytes.push(resist_val);
            resist_opt = Some(resist_val);
        }

        let (mut total_energy_opt, mut energy_hour_opt, mut energy_min_opt) = (None, None, None);
        if f_energy {
            bytes.extend_from_slice(&energy_total_val.to_le_bytes());
            bytes.extend_from_slice(&energy_hour_val.to_le_bytes());
            bytes.push(energy_min_val);
            total_energy_opt = super::none_if_eq(energy_total_val, 0xFFFF);
            energy_hour_opt = super::none_if_eq(energy_hour_val, 0xFFFF);
            energy_min_opt = super::none_if_eq(energy_min_val, 0xFF);
        }

        let mut hr_opt = None;
        if f_hr {
            bytes.push(hr_val);
            hr_opt = Some(hr_val);
        }

        let mut met_opt = None;
        if f_met {
            bytes.push(met_val);
            met_opt = Some(met_val);
        }

        let mut elapsed_opt = None;
        if f_elapsed {
            bytes.extend_from_slice(&elapsed_val.to_le_bytes());
            elapsed_opt = Some(elapsed_val);
        }

        let mut remaining_opt = None;
        if f_remaining {
            bytes.extend_from_slice(&remaining_val.to_le_bytes());
            remaining_opt = Some(remaining_val);
        }

        let fragment = RowerFragment {
            flags,
            more_data,
            stroke_rate_half_spm,
            stroke_count: stroke_count_opt,
            avg_stroke_rate_half_spm: avg_spm_opt,
            total_distance_m: dist_opt,
            inst_pace_s_per_500m: inst_pace_opt,
            avg_pace_s_per_500m: avg_pace_opt,
            inst_power_w: inst_power_opt,
            avg_power_w: avg_power_opt,
            resistance_level: resist_opt,
            total_energy_kcal: total_energy_opt,
            energy_per_hour_kcal: energy_hour_opt,
            energy_per_minute_kcal: energy_min_opt,
            heart_rate_bpm: hr_opt,
            metabolic_equiv_tenths: met_opt,
            elapsed_time_s: elapsed_opt,
            remaining_time_s: remaining_opt,
        };

        (bytes, fragment)
    }

    prop_compose! {
        fn arb_fragment_bytes_and_expected()
        (
            more_data in any::<bool>(),
            f_avg_spm in any::<bool>(),
            f_dist in any::<bool>(),
            f_inst_pace in any::<bool>(),
            f_avg_pace in any::<bool>(),
            f_inst_power in any::<bool>(),
            f_avg_power in any::<bool>(),
            f_resist in any::<bool>(),
            f_energy in any::<bool>(),
            f_hr in any::<bool>(),
            f_met in any::<bool>(),
            f_elapsed in any::<bool>(),
            f_remaining in any::<bool>(),
            sr_half in any::<u8>(),
            stroke_count in any::<u16>(),
            avg_spm_val in any::<u8>(),
            dist_raw in any::<u32>(),
            inst_pace_val in any::<u16>(),
            avg_pace_val in any::<u16>(),
            inst_power_val in any::<i16>(),
            avg_power_val in any::<i16>(),
            resist_val in any::<u8>(),
            energy_total_val in any::<u16>(),
            energy_hour_val in any::<u16>(),
            energy_min_val in any::<u8>(),
            hr_val in any::<u8>(),
            met_val in any::<u8>(),
            elapsed_val in any::<u16>(),
            remaining_val in any::<u16>(),
        )
        -> (Vec<u8>, RowerFragment) {
            build_fragment(
                more_data,
                f_avg_spm,
                f_dist,
                f_inst_pace,
                f_avg_pace,
                f_inst_power,
                f_avg_power,
                f_resist,
                f_energy,
                f_hr,
                f_met,
                f_elapsed,
                f_remaining,
                sr_half,
                stroke_count,
                avg_spm_val,
                dist_raw,
                inst_pace_val,
                avg_pace_val,
                inst_power_val,
                avg_power_val,
                resist_val,
                energy_total_val,
                energy_hour_val,
                energy_min_val,
                hr_val,
                met_val,
                elapsed_val,
                remaining_val,
            )
        }
    }

    proptest! {
        #[test]
        fn prop_parse_matches_expected((bytes, expected) in arb_fragment_bytes_and_expected()) {
            let (rem, got) = parse_rower_fragment(&bytes)
                .map_err(|e| TestCaseError::fail(format!("parse error: {e:?} bytes={:02X?}", bytes)))?;

            prop_assert!(rem.is_empty(), "parser left trailing bytes: {:02X?}", rem);
            prop_assert_eq!(got.flags, expected.flags);
            prop_assert_eq!(got.more_data, expected.more_data);
            prop_assert_eq!(got.stroke_rate_half_spm, expected.stroke_rate_half_spm);
            prop_assert_eq!(got.stroke_count, expected.stroke_count);
            prop_assert_eq!(got.avg_stroke_rate_half_spm, expected.avg_stroke_rate_half_spm);
            prop_assert_eq!(got.total_distance_m, expected.total_distance_m);
            prop_assert_eq!(got.inst_pace_s_per_500m, expected.inst_pace_s_per_500m);
            prop_assert_eq!(got.avg_pace_s_per_500m, expected.avg_pace_s_per_500m);
            prop_assert_eq!(got.inst_power_w, expected.inst_power_w);
            prop_assert_eq!(got.avg_power_w, expected.avg_power_w);
            prop_assert_eq!(got.resistance_level, expected.resistance_level);
            prop_assert_eq!(got.total_energy_kcal, expected.total_energy_kcal);
            prop_assert_eq!(got.energy_per_hour_kcal, expected.energy_per_hour_kcal);
            prop_assert_eq!(got.energy_per_minute_kcal, expected.energy_per_minute_kcal);
            prop_assert_eq!(got.heart_rate_bpm, expected.heart_rate_bpm);
            prop_assert_eq!(got.metabolic_equiv_tenths, expected.metabolic_equiv_tenths);
            prop_assert_eq!(got.elapsed_time_s, expected.elapsed_time_s);
            prop_assert_eq!(got.remaining_time_s, expected.remaining_time_s);
        }
    }

    prop_compose! {
        #[allow(clippy::type_complexity)]
        fn arb_two_fragment_record()
        (
            f1_avg_spm in any::<bool>(),
            f1_dist in any::<bool>(),
            f1_inst_pace in any::<bool>(),
            f1_avg_pace in any::<bool>(),
            f1_inst_power in any::<bool>(),
            f1_avg_power in any::<bool>(),
            f1_resist in any::<bool>(),
            f1_energy in any::<bool>(),
            f1_hr in any::<bool>(),
            f1_met in any::<bool>(),
            f1_elapsed in any::<bool>(),
            f1_remaining in any::<bool>(),

            f2_avg_spm in any::<bool>(),
            f2_dist in any::<bool>(),
            f2_inst_pace in any::<bool>(),
            f2_avg_pace in any::<bool>(),
            f2_inst_power in any::<bool>(),
            f2_avg_power in any::<bool>(),
            f2_resist in any::<bool>(),
            f2_energy in any::<bool>(),
            f2_hr in any::<bool>(),
            f2_met in any::<bool>(),
            f2_elapsed in any::<bool>(),
            f2_remaining in any::<bool>(),

            sr_half in any::<u8>(),
            stroke_count in any::<u16>(),

            avg_spm1 in any::<u8>(),
            avg_spm2 in any::<u8>(),

            dist1 in any::<u32>(),
            dist2 in any::<u32>(),

            inst_pace1 in any::<u16>(),
            inst_pace2 in any::<u16>(),

            avg_pace1 in any::<u16>(),
            avg_pace2 in any::<u16>(),

            inst_power1 in any::<i16>(),
            inst_power2 in any::<i16>(),

            avg_power1 in any::<i16>(),
            avg_power2 in any::<i16>(),

            resist1 in any::<u8>(),
            resist2 in any::<u8>(),

            energy_total1 in any::<u16>(),
            energy_total2 in any::<u16>(),
            energy_hour1 in any::<u16>(),
            energy_hour2 in any::<u16>(),
            energy_min1 in any::<u8>(),
            energy_min2 in any::<u8>(),

            hr1 in any::<u8>(),
            hr2 in any::<u8>(),
            met1 in any::<u8>(),
            met2 in any::<u8>(),

            elapsed1 in any::<u16>(),
            elapsed2 in any::<u16>(),
            remaining1 in any::<u16>(),
            remaining2 in any::<u16>(),
        )
        -> (Vec<u8>, Vec<u8>, RowerRecord) {
            let (bytes1, frag1) = build_fragment(
                true,
                f1_avg_spm,
                f1_dist,
                f1_inst_pace,
                f1_avg_pace,
                f1_inst_power,
                f1_avg_power,
                f1_resist,
                f1_energy,
                f1_hr,
                f1_met,
                f1_elapsed,
                f1_remaining,
                sr_half,
                stroke_count,
                avg_spm1,
                dist1,
                inst_pace1,
                avg_pace1,
                inst_power1,
                avg_power1,
                resist1,
                energy_total1,
                energy_hour1,
                energy_min1,
                hr1,
                met1,
                elapsed1,
                remaining1,
            );

            let (bytes2, frag2) = build_fragment(
                false,
                f2_avg_spm,
                f2_dist,
                f2_inst_pace,
                f2_avg_pace,
                f2_inst_power,
                f2_avg_power,
                f2_resist,
                f2_energy,
                f2_hr,
                f2_met,
                f2_elapsed,
                f2_remaining,
                sr_half,
                stroke_count,
                avg_spm2,
                dist2,
                inst_pace2,
                avg_pace2,
                inst_power2,
                avg_power2,
                resist2,
                energy_total2,
                energy_hour2,
                energy_min2,
                hr2,
                met2,
                elapsed2,
                remaining2,
            );

            let expected = RowerRecord {
                flags: (frag1.flags | frag2.flags) & !1,
                stroke_rate_half_spm: frag2.stroke_rate_half_spm.or(frag1.stroke_rate_half_spm),
                stroke_count: frag2.stroke_count.or(frag1.stroke_count),
                avg_stroke_rate_half_spm: frag2
                    .avg_stroke_rate_half_spm
                    .or(frag1.avg_stroke_rate_half_spm),
                total_distance_m: frag2.total_distance_m.or(frag1.total_distance_m),
                inst_pace_s_per_500m: frag2
                    .inst_pace_s_per_500m
                    .or(frag1.inst_pace_s_per_500m),
                avg_pace_s_per_500m: frag2
                    .avg_pace_s_per_500m
                    .or(frag1.avg_pace_s_per_500m),
                inst_power_w: frag2.inst_power_w.or(frag1.inst_power_w),
                avg_power_w: frag2.avg_power_w.or(frag1.avg_power_w),
                resistance_level: frag2.resistance_level.or(frag1.resistance_level),
                total_energy_kcal: frag2.total_energy_kcal.or(frag1.total_energy_kcal),
                energy_per_hour_kcal: frag2
                    .energy_per_hour_kcal
                    .or(frag1.energy_per_hour_kcal),
                energy_per_minute_kcal: frag2
                    .energy_per_minute_kcal
                    .or(frag1.energy_per_minute_kcal),
                heart_rate_bpm: frag2.heart_rate_bpm.or(frag1.heart_rate_bpm),
                metabolic_equiv_tenths: frag2
                    .metabolic_equiv_tenths
                    .or(frag1.metabolic_equiv_tenths),
                elapsed_time_s: frag2.elapsed_time_s.or(frag1.elapsed_time_s),
                remaining_time_s: frag2.remaining_time_s.or(frag1.remaining_time_s),
            };

            (bytes1, bytes2, expected)
        }
    }

    proptest! {
        #[test]
        fn prop_assembler_merges_correctly((bytes1, bytes2, expected) in arb_two_fragment_record()) {
            let (rem1, frag1) = parse_rower_fragment(&bytes1)
                .map_err(|e| TestCaseError::fail(format!("fragment1 parse error: {e:?} bytes={:02X?}", bytes1)))?;
            prop_assert!(rem1.is_empty(), "fragment1 trailing bytes: {:02X?}", rem1);
            prop_assert!(frag1.more_data, "fragment1 should have more_data=true");

            let (rem2, frag2) = parse_rower_fragment(&bytes2)
                .map_err(|e| TestCaseError::fail(format!("fragment2 parse error: {e:?} bytes={:02X?}", bytes2)))?;
            prop_assert!(rem2.is_empty(), "fragment2 trailing bytes: {:02X?}", rem2);
            prop_assert!(!frag2.more_data, "fragment2 should have more_data=false");

            let mut assembler = RowerAssembler::default();
            prop_assert!(assembler.push(frag1).is_none());
            let record = assembler
                .push(frag2)
                .expect("final fragment should emit a record");

            prop_assert_eq!(record.flags, expected.flags);
            prop_assert_eq!(record.stroke_rate_half_spm, expected.stroke_rate_half_spm);
            prop_assert_eq!(record.stroke_count, expected.stroke_count);
            prop_assert_eq!(
                record.avg_stroke_rate_half_spm,
                expected.avg_stroke_rate_half_spm
            );
            prop_assert_eq!(record.total_distance_m, expected.total_distance_m);
            prop_assert_eq!(
                record.inst_pace_s_per_500m,
                expected.inst_pace_s_per_500m
            );
            prop_assert_eq!(record.avg_pace_s_per_500m, expected.avg_pace_s_per_500m);
            prop_assert_eq!(record.inst_power_w, expected.inst_power_w);
            prop_assert_eq!(record.avg_power_w, expected.avg_power_w);
            prop_assert_eq!(record.resistance_level, expected.resistance_level);
            prop_assert_eq!(record.total_energy_kcal, expected.total_energy_kcal);
            prop_assert_eq!(
                record.energy_per_hour_kcal,
                expected.energy_per_hour_kcal
            );
            prop_assert_eq!(
                record.energy_per_minute_kcal,
                expected.energy_per_minute_kcal
            );
            prop_assert_eq!(record.heart_rate_bpm, expected.heart_rate_bpm);
            prop_assert_eq!(
                record.metabolic_equiv_tenths,
                expected.metabolic_equiv_tenths
            );
            prop_assert_eq!(record.elapsed_time_s, expected.elapsed_time_s);
            prop_assert_eq!(record.remaining_time_s, expected.remaining_time_s);
        }
    }
}
