// SPDX-License-Identifier: MIT
//
// FIXME: remove this once we have something that doesn't scream hundreds of warnings
#![allow(unused_variables)]
#![allow(dead_code)]

use std::ops::{Range, RangeInclusive};
use thiserror::Error;

pub mod hid;
pub mod hut;
pub mod types;

use hid::*;
pub use types::*;

/// Implements `From<Foo> for Bar` to call `From<&Foo> for Bar`
macro_rules! impl_from_without_ref {
    ($tipo:ty, $to_expr:ident, $to:ty) => {
        impl From<$tipo> for $to {
            fn from(f: $tipo) -> $to {
                $to_expr::from(&f)
            }
        }
    };
}

/// Calculates the two's complement for a value with
/// a given number of of bits.
trait TwosComplement<To> {
    /// Returns the two's complement for a value
    /// with a given number of bits.
    fn twos_comp(self, nbits: usize) -> To;
}

// RangeInclusive doesn't implement ExactSizeIterator for usize and that
// trait is outside our crate, so let's add our own trait so we can
// implement RangeInclusive::len().
trait Length {
    fn len(self) -> usize;
}

/// A trait to signal that the size of this object is in bits
/// and/or bytes.
///
/// This is not [Sized] but represents the size of this object on the wire, e.g.
/// a HID report's size.
pub trait BitSize {
    /// The size in bits for this object. Where [BitSize::size_in_bits] is
    /// not a multiple of 8, the [BitSize::size_in_bytes] is rounded up to fit all bits.
    fn size_in_bits(&self) -> usize;
    /// The size in bytes for this object. Where [BitSize::size_in_bits] is
    /// not a multiple of 8, the [BitSize::size_in_bytes] is rounded up to fit all bits.
    fn size_in_bytes(&self) -> usize;
}

// RangeInclusive doesn't implement ExactSizeIterator for usize and that
// trait is outside our crate, so...
impl Length for &RangeInclusive<usize> {
    fn len(self) -> usize {
        self.end() - self.start() + 1
    }
}

impl TwosComplement<i8> for u8 {
    fn twos_comp(self, nbits: usize) -> i8 {
        assert!(nbits > 0);
        if nbits >= 8 || self & (1 << (nbits - 1)) == 0 {
            self as i8
        } else {
            let s = self as i16;
            let min = 1 << nbits;
            (-min + s) as i8
        }
    }
}

impl TwosComplement<i16> for u16 {
    fn twos_comp(self, nbits: usize) -> i16 {
        assert!(nbits > 0);
        if nbits >= 16 || self & (1 << (nbits - 1)) == 0 {
            self as i16
        } else {
            let s = self as i32;
            let min = 1 << nbits;
            (-min + s) as i16
        }
    }
}

impl TwosComplement<i32> for u32 {
    fn twos_comp(self, nbits: usize) -> i32 {
        assert!(nbits > 0);
        if nbits >= 32 || self & (1 << (nbits - 1)) == 0 {
            self as i32
        } else {
            let s = self as i64;
            let min = 1 << nbits;
            (-min + s) as i32
        }
    }
}

/// A [ReportDescriptor] is the static set of [Items](hid::Item)
/// that define how data from the device should be interpreted.
///
/// A device may have up to three different types of [Reports](Report)
/// (Input, Output, and Feature), all of which are defined in the
/// single report descriptor.
///
/// ```
/// # use hidreport::*;
/// # let bytes: &[u8] = &[0x05, 0x01, 0x09, 0x02, 0xa1, 0x01, 0x05, 0x01, 0x09, 0x02, 0xa1, 0x02, 0x85, 0x1a, 0x09, 0x01, 0xa1, 0x00, 0x05, 0x09, 0x19, 0x01, 0x29, 0x05, 0x95, 0x05, 0x75, 0x01, 0x15, 0x00, 0x25, 0x01, 0x81, 0x02, 0x75, 0x03, 0x95, 0x01, 0x81, 0x01, 0x05, 0x01, 0x09, 0x30, 0x09, 0x31, 0x95, 0x02, 0x75, 0x10, 0x16, 0x01, 0x80, 0x26, 0xff, 0x7f, 0x81, 0x06, 0xa1, 0x02, 0x85, 0x12, 0x09, 0x48, 0x95, 0x01, 0x75, 0x02, 0x15, 0x00, 0x25, 0x01, 0x35, 0x01, 0x45, 0x0c, 0xb1, 0x02, 0x85, 0x1a, 0x09, 0x38, 0x35, 0x00, 0x45, 0x00, 0x95, 0x01, 0x75, 0x10, 0x16, 0x01, 0x80, 0x26, 0xff, 0x7f, 0x81, 0x06, 0xc0, 0xa1, 0x02, 0x85, 0x12, 0x09, 0x48, 0x75, 0x02, 0x15, 0x00, 0x25, 0x01, 0x35, 0x01, 0x45, 0x0c, 0xb1, 0x02, 0x35, 0x00, 0x45, 0x00, 0x75, 0x04, 0xb1, 0x01, 0x85, 0x1a, 0x05, 0x0c, 0x95, 0x01, 0x75, 0x10, 0x16, 0x01, 0x80, 0x26, 0xff, 0x7f, 0x0a, 0x38, 0x02, 0x81, 0x06, 0xc0, 0xc0, 0xc0, 0xc0, 0x05, 0x0c, 0x09, 0x01, 0xa1, 0x01, 0x05, 0x01, 0x09, 0x02, 0xa1, 0x02, 0x85, 0x1f, 0x05, 0x0c, 0x0a, 0x38, 0x02, 0x95, 0x01, 0x75, 0x10, 0x16, 0x01, 0x80, 0x26, 0xff, 0x7f, 0x81, 0x06, 0x85, 0x17, 0x06, 0x00, 0xff, 0x0a, 0x06, 0xff, 0x0a, 0x0f, 0xff, 0x15, 0x00, 0x25, 0x01, 0x35, 0x01, 0x45, 0x0c, 0x95, 0x02, 0x75, 0x02, 0xb1, 0x02, 0x0a, 0x04, 0xff, 0x35, 0x00, 0x45, 0x00, 0x95, 0x01, 0x75, 0x01, 0xb1, 0x02, 0x75, 0x03, 0xb1, 0x01, 0xc0, 0xc0];
/// # let input: &[u8] = &[0x1a, 0x00, 0xff, 0xff, 0xfe, 0xff, 00, 00, 00, 0x00];
/// let rdesc: ReportDescriptor = ReportDescriptor::try_from(bytes).unwrap();
/// for r in rdesc.input_reports() {
///     println!("Input Report with report ID: {:?}", r.report_id());
/// }
/// let report: InputReport = rdesc.parse_input_report(input).unwrap();
/// println!("This is an input report for report ID: {:?}", report.report_id());
/// println!("Fields {:?} is of value {}",
///          report.fields()[0].usages(),
///          report[0]);
/// ```
///
#[derive(Debug, Default)]
pub struct ReportDescriptor {
    input_reports: Vec<RDescReport>,
    output_reports: Vec<RDescReport>,
    feature_reports: Vec<RDescReport>,
}

impl<'a> ReportDescriptor {
    /// Returns the set of input reports or the empty
    /// slice if none exist.
    pub fn input_reports(&self) -> &[impl Report] {
        &self.input_reports
    }

    /// Returns the set of output reports or the empty
    /// slice if none exist.
    pub fn output_reports(&self) -> &[impl Report] {
        &self.output_reports
    }

    /// Returns the set of feature reports or the empty
    /// slice if none exist.
    pub fn feature_reports(&self) -> &[impl Report] {
        &self.feature_reports
    }

    /// Parse the given bytes as input report.
    ///
    /// The first byte of the report must be the Report ID
    /// if this [ReportDescriptor] defined Report IDs.
    pub fn parse_input_report(&'a self, bytes: &[u8]) -> Result<InputReport> {
        let list = &self.input_reports;
        let parsed = self.parse_report(list, bytes)?;
        Ok(InputReport {
            report: parsed.report,
            values: parsed.values,
        })
    }

    /// Parse the given bytes as output report.
    ///
    /// The first byte of the report must be the Report ID
    /// if this [ReportDescriptor] defined Report IDs.
    pub fn parse_output_report(&'a self, bytes: &[u8]) -> Result<OutputReport> {
        let list = &self.output_reports;
        let parsed = self.parse_report(list, bytes)?;
        Ok(OutputReport {
            report: parsed.report,
            values: parsed.values,
        })
    }

    /// Parse the given bytes as feature report.
    ///
    /// The first byte of the report must be the Report ID
    /// if this [ReportDescriptor] defined Report IDs.
    pub fn parse_feature_report(&'a self, bytes: &[u8]) -> Result<FeatureReport> {
        let list = &self.feature_reports;
        let parsed = self.parse_report(list, bytes)?;
        Ok(FeatureReport {
            report: parsed.report,
            values: parsed.values,
        })
    }

    /// Parse a byte sequence and return the values together
    /// with the report these values belong to.
    fn parse_report(&'a self, list: &'a [RDescReport], bytes: &[u8]) -> Result<ParsedReport> {
        // Do we have report IDs? If not, the first report is what we want.
        let report = if list.first().unwrap().report_id().is_some() {
            list.iter()
                .find(|r| r.report_id().unwrap() == ReportId(bytes[0]))
                .expect("Unknown report ID")
        } else {
            list.first().unwrap()
        };

        let values = report.parse(bytes)?;
        let parsed = ParsedReport { report, values };
        Ok(parsed)
    }
}

impl TryFrom<&[u8]> for ReportDescriptor {
    type Error = ParserError;

    /// Try to parse the given byte array as a report descriptor.
    fn try_from(bytes: &[u8]) -> Result<ReportDescriptor> {
        parse_report_descriptor(bytes)
    }
}

/// A single value as defined by a [ReportDescriptor]'s [Field].
///
/// Use the various [From] implementations to cast this into the
/// expected target field. These are provided for convenience only
/// they are all the respective equivalent of `value as i16`, etc.:
///
/// ```
/// # use hidreport::ReportValue;
/// fn func(val: &ReportValue) {
///     assert_eq!(u32::from(val) as i32, i32::from(val));
///     assert_eq!(u32::from(val) as i16, i16::from(val));
///     assert_eq!(u32::from(val) as i8, i8::from(val));
///     assert_eq!(u32::from(val) as u16, u16::from(val));
///     assert_eq!(u32::from(val) as u8, u8::from(val));
/// }
/// ```
///
/// It is up to the caller to verify the value fits into the
/// data size.
#[derive(Debug)]
pub enum ReportValue {
    Signed(i32),
    Unsigned(u32),
}

impl ReportValue {
    fn as_u32(&self) -> u32 {
        match self {
            ReportValue::Signed(i) => *i as u32,
            ReportValue::Unsigned(u) => *u,
        }
    }

    fn as_i32(&self) -> i32 {
        match self {
            ReportValue::Signed(i) => *i,
            ReportValue::Unsigned(u) => *u as i32,
        }
    }
}

impl std::fmt::LowerHex for ReportValue {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{:x}", self.as_u32())
    }
}

impl std::fmt::Display for ReportValue {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            ReportValue::Signed(i) => write!(f, "{i}"),
            ReportValue::Unsigned(u) => write!(f, "{u}"),
        }
    }
}

impl From<&ReportValue> for u32 {
    fn from(r: &ReportValue) -> u32 {
        r.as_u32()
    }
}

impl_from_without_ref!(ReportValue, u32, u32);

impl From<&ReportValue> for i32 {
    fn from(r: &ReportValue) -> i32 {
        r.as_i32()
    }
}

impl_from_without_ref!(ReportValue, i32, i32);

impl From<&ReportValue> for u16 {
    fn from(r: &ReportValue) -> u16 {
        r.as_u32() as u16
    }
}

impl_from_without_ref!(ReportValue, u16, u16);

impl From<&ReportValue> for i16 {
    fn from(r: &ReportValue) -> i16 {
        r.as_i32() as i16
    }
}

impl_from_without_ref!(ReportValue, i16, i16);

impl From<&ReportValue> for u8 {
    fn from(r: &ReportValue) -> u8 {
        r.as_u32() as u8
    }
}

impl_from_without_ref!(ReportValue, u8, u8);

impl From<&ReportValue> for i8 {
    fn from(r: &ReportValue) -> i8 {
        r.as_i32() as i8
    }
}

impl_from_without_ref!(ReportValue, i8, i8);

/// The result of parsing a [Report] via
/// [ReportDescriptor::parse_input_report].
///
/// This struct wraps the [Report] as well as
/// the contained [ReportValues](ReportValue).
#[derive(Debug)]
pub struct InputReport<'a> {
    report: &'a RDescReport,
    values: Vec<ReportValue>,
}

impl<'a> Report for InputReport<'a> {
    fn report_id(&self) -> &Option<ReportId> {
        self.report.report_id()
    }

    fn fields(&self) -> &[Field] {
        self.report.fields()
    }
}

impl<'a> BitSize for InputReport<'a> {
    fn size_in_bits(&self) -> usize {
        self.report.size_in_bits()
    }
    fn size_in_bytes(&self) -> usize {
        self.report.size_in_bytes()
    }
}

impl<'a> std::ops::Deref for InputReport<'a> {
    type Target = [ReportValue];

    fn deref(&self) -> &Self::Target {
        &self.values
    }
}

/// The result of parsing a [Report] via
/// [ReportDescriptor::parse_output_report]
pub struct OutputReport<'a> {
    report: &'a RDescReport,
    values: Vec<ReportValue>,
}

impl<'a> Report for OutputReport<'a> {
    fn report_id(&self) -> &Option<ReportId> {
        self.report.report_id()
    }

    fn fields(&self) -> &[Field] {
        self.report.fields()
    }
}

impl<'a> BitSize for OutputReport<'a> {
    fn size_in_bits(&self) -> usize {
        self.report.size_in_bits()
    }
    fn size_in_bytes(&self) -> usize {
        self.report.size_in_bytes()
    }
}

impl<'a> std::ops::Deref for OutputReport<'a> {
    type Target = [ReportValue];

    fn deref(&self) -> &Self::Target {
        &self.values
    }
}

/// The result of parsing a [Report] via
/// [ReportDescriptor::parse_feature_report]
pub struct FeatureReport<'a> {
    report: &'a RDescReport,
    values: Vec<ReportValue>,
}

impl<'a> Report for FeatureReport<'a> {
    fn report_id(&self) -> &Option<ReportId> {
        self.report.report_id()
    }

    fn fields(&self) -> &[Field] {
        self.report.fields()
    }
}

impl<'a> BitSize for FeatureReport<'a> {
    fn size_in_bits(&self) -> usize {
        self.report.size_in_bits()
    }
    fn size_in_bytes(&self) -> usize {
        self.report.size_in_bytes()
    }
}

impl<'a> std::ops::Deref for FeatureReport<'a> {
    type Target = [ReportValue];

    fn deref(&self) -> &Self::Target {
        &self.values
    }
}

/// The result of parsing a [Report] via
/// [ReportDescriptor::parse_input_report],
/// [ReportDescriptor::parse_output_report],
/// [ReportDescriptor::parse_feature_report], or [Report::parse].
#[derive(Debug)]
struct ParsedReport<'a> {
    report: &'a RDescReport,
    values: Vec<ReportValue>,
}

#[derive(Copy, Clone, Debug)]
pub enum Direction {
    Input,
    Output,
    Feature,
}

/// A HID Input, Output or Feature Report.
///
/// Where a report contains the [Report::report_id] the first
/// byte of the report is always that Report ID, followed
/// by the data in the sequence announced in the HID [ReportDescriptor].
///
/// Note that each of Input, Output and Feature Reports
/// have their own enumeration of Report IDs, i.e. an Input Report
/// with a Report ID of e.g. 1 may have a different size and/or [Field]s
/// to an Output Report with a Report ID of 1.
///
/// The Report ID has no meaning other than to distinguish
/// different reports. See Section 6.2.2.7 for details.
pub trait Report: BitSize {
    /// Returns the HID Report ID for this report, if any.
    fn report_id(&self) -> &Option<ReportId>;

    /// Returns the parsed HID Fields ID for this report. A caller should
    /// iterate through these fields to find the ones it is interested
    /// in and use the [Field::bits] to extract the data from future
    /// reports.
    fn fields(&self) -> &[Field];
}

/// A HID Input, Output or Feature Report.
///
/// Where a report contains the [Report::report_id] the first
/// byte of the report is always that Report ID, followed
/// by the data in the sequence announced in the HID [ReportDescriptor].
///
/// Note that each of Input, Output and Feature Reports
/// have their own enumeration of Report IDs, i.e. an Input Report
/// with a Report ID of e.g. 1 may have a different size and/or [Field]s
/// to an Output Report with a Report ID of 1.
///
/// The Report ID has no meaning other than to distinguish
/// different reports. See Section 6.2.2.7 for details.
#[derive(Debug)]
struct RDescReport {
    /// The report ID, if any
    id: Option<ReportId>,
    /// The size of this report in bits
    size: usize,
    /// The fields present in this report
    fields: Vec<Field>,
}

impl Report for RDescReport {
    fn report_id(&self) -> &Option<ReportId> {
        &self.id
    }

    fn fields(&self) -> &[Field] {
        &self.fields
    }
}

impl<'a> RDescReport {
    /// Extract the bit range from the given byte array, converting the
    /// result into a [u32].
    ///
    /// The number of bits in the range must be less or equal to 32.
    fn extract_u32(bytes: &[u8], bits: &RangeInclusive<usize>) -> u32 {
        let nbits = bits.len();
        assert_ne!(nbits, 0);
        assert!(nbits <= 32);
        // If we start at a bit 0 we only need 1 byte (for u8)
        // if we start at anything else, we need the next byte(s) too
        let bytecount = if bits.start() % 8 == 0 {
            (nbits + 7) / 8
        } else {
            (nbits + 7) / 8 + 1
        };
        let base_index = bits.start() / 8;
        let bytes = &bytes[base_index..base_index + bytecount];
        //println!("---------------------------------");
        //println!("In bytes are: {bytes:x?}");
        let value: u64 = Range {
            start: 0u64,
            end: bytes.len() as u64,
        }
        //.inspect(|idx| println!("Accessing index {idx}: {:x?}", bytes[*idx as usize]))
        .fold(0u64, |acc: u64, idx| {
            //println!("acc is {acc}, idx is {idx}");
            //println!("bytes[idx] is {:x}", bytes[idx as usize] as u64);
            acc | (bytes[idx as usize] as u64) << (8 * idx)
        });
        //println!("Value is thus: {value:x?}");

        let base_shift = bits.start() % 8;
        let mask_shift = 32 - nbits;
        let mask = (!0 as u32) >> mask_shift;
        //println!("Mask is : {mask:x?}");
        let value = (value >> base_shift) as u32;
        //println!("{base_shift}-shifted value  is : {value:x?}");

        //println!("---------------------------------");
        value & mask
    }

    /// Extract the bit range from the given byte array, converting the
    /// result into a [i32]. The sign of the number matches that
    /// of the given bit range, e.g. a bit range of length 4 with the MSB set
    /// to 1 will result in a negative number, up-casted to [i32].
    ///
    /// The number of bits in the range must be less or equal to 32.
    fn extract_i32(bytes: &[u8], bits: &RangeInclusive<usize>) -> i32 {
        let nbits = bits.len();
        let v = Self::extract_u32(bytes, bits);
        v.twos_comp(nbits)
    }

    fn extract_u16(bytes: &[u8], bits: &RangeInclusive<usize>) -> u16 {
        assert!(bits.len() <= 16);
        let v: u32 = Self::extract_u32(bytes, bits);
        v as u16
    }

    fn extract_i16(bytes: &[u8], bits: &RangeInclusive<usize>) -> i16 {
        let nbits = bits.len();
        let v = Self::extract_u16(bytes, bits);
        v.twos_comp(nbits)
    }

    fn extract_u8(bytes: &[u8], bits: &RangeInclusive<usize>) -> u8 {
        assert!(bits.len() <= 8);
        let v: u32 = Self::extract_u32(bytes, bits);
        v as u8
    }

    fn extract_i8(bytes: &[u8], bits: &RangeInclusive<usize>) -> i8 {
        let nbits = bits.len();
        let v = Self::extract_u8(bytes, bits);
        v.twos_comp(nbits)
    }

    /// Parse the given bytes into a set of [ReportValue]s. Each of these
    /// values matches the corresponding [Field] in [Report::fields].
    pub fn parse(&'a self, bytes: &[u8]) -> Result<Vec<ReportValue>> {
        let values: Vec<ReportValue> = self
            .fields()
            .iter()
            .map(|f| {
                (
                    f.bits(),
                    match f {
                        Field::Variable(f) => f.logical_range,
                        Field::Array(f) => f.logical_range,
                        Field::Constant(_) => LogicalRange {
                            minimum: LogicalMinimum(0),
                            maximum: LogicalMaximum(0),
                        },
                    },
                )
            })
            .map(|(bits, range)| {
                if range.minimum < LogicalMinimum(0) {
                    ReportValue::Signed(match bits.len() {
                        1..=7 => Self::extract_i8(bytes, bits) as i32,
                        8..=15 => Self::extract_i16(bytes, bits) as i32,
                        16..=31 => Self::extract_i32(bytes, bits),
                        n => panic!("invalid data length {n}"),
                    })
                } else {
                    ReportValue::Unsigned(match bits.len() {
                        1..=7 => Self::extract_u8(bytes, bits) as u32,
                        8..=15 => Self::extract_u16(bytes, bits) as u32,
                        16..=31 => Self::extract_u32(bytes, bits),
                        n => panic!("invalid data length {n}"),
                    })
                }
            })
            // .inspect(|v| println!("{v:?}"))
            .collect();

        Ok(values)
    }
}

impl BitSize for RDescReport {
    /// The size of this HID report on the wire, in bits
    fn size_in_bits(&self) -> usize {
        self.size
    }

    /// The size of this HID report on the wire, in bytes.
    fn size_in_bytes(&self) -> usize {
        self.size / 8
    }
}

/// The usage of a [Field] defines the interpretation of a
/// data value. See the [hut] module for a list of known Usages.
///
/// A Usage comprises of a 16 bit [UsagePage] and a 16 bit [UsageId].
#[derive(Clone, Copy, Debug)]
pub struct Usage {
    pub usage_page: UsagePage,
    pub usage_id: UsageId,
}

/// The logical range of a [Field]s' value, see Section 5.8.
///
/// Values sent to/fro a device fit within this minimum and
/// (inclusive) maximum range.
///
/// Interpretation of the data is as signed value if one of
/// minimum or maximum is less than zero, otherwise the
/// value is unsigned.
///
/// See [ReportValue::unsigned] and [ReportValue::signed].
#[derive(Clone, Copy, Debug)]
pub struct LogicalRange {
    pub minimum: LogicalMinimum,
    pub maximum: LogicalMaximum,
}

/// The physical range of a [Field]s' value, see Section 6.2.2.7.
///
/// The physical range (if it exists) maps the logical range
/// into a physical dimension so that the logical minimum represents
/// the physical minimum and the logical maximum represents the
/// physical maximum value.
#[derive(Clone, Copy, Debug)]
pub struct PhysicalRange {
    pub minimum: PhysicalMinimum,
    pub maximum: PhysicalMaximum,
}

/// A single field inside a [Report].
///
/// Fields may be [Field::Variable] and represent a
/// single element of data or they may be
/// a [Field::Array] that represent
/// multiple elements.
///
/// Fields of type [Field::Constant] should be ignored by
/// the caller.
#[derive(Clone, Debug)]
pub enum Field {
    Variable(VariableField),
    Array(ArrayField),
    Constant(ConstantField),
}

impl Field {
    /// Returns the bit range that make up this field.
    pub fn bits(&self) -> &RangeInclusive<usize> {
        match self {
            Field::Variable(f) => &f.bits,
            Field::Array(f) => &f.bits,
            Field::Constant(f) => &f.bits,
        }
    }

    /// Returns the Report ID this field belongs to, if any.
    fn report_id(&self) -> &Option<ReportId> {
        match self {
            Field::Variable(f) => &f.report_id,
            Field::Array(f) => &f.report_id,
            Field::Constant(f) => &f.report_id,
        }
    }

    fn update_bit_offset(&mut self, offset: usize) {
        let r = self.bits();
        let r = RangeInclusive::new(offset + r.start(), offset + r.end());
        match self {
            Field::Variable(f) => f.bits = r,
            Field::Array(f) => f.bits = r,
            Field::Constant(f) => f.bits = r,
        };
    }

    pub fn usages(&self) -> &[Usage] {
        match self {
            Field::Variable(f) => f.usages(),
            Field::Array(f) => f.usages(),
            Field::Constant(f) => f.usages(),
        }
    }
}

impl Length for &Field {
    fn len(self) -> usize {
        return self.bits().len();
    }
}

/// A [VariableField] represents a single physical control.
#[derive(Clone, Debug)]
pub struct VariableField {
    pub report_id: Option<ReportId>,
    pub direction: Direction,
    pub bits: RangeInclusive<usize>,
    usages: Vec<Usage>,
    pub logical_range: LogicalRange,
    pub physical_range: Option<PhysicalRange>,
    pub unit: Option<Unit>,
    pub unit_exponent: Option<UnitExponent>,
    pub collections: Vec<Collection>,
}

impl VariableField {
    pub fn usage(&self) -> &Usage {
        self.usages.first().unwrap()
    }

    pub fn usages(&self) -> &[Usage] {
        &self.usages
    }
}

/// An [ArrayField] represents a group of physical controls,
/// see section 6.2.2.5.
///
/// > An array provides an alternate means for
/// > describing the data returned from a group of
/// > buttons. Arrays are more efficient, if less flexible
/// > than variable items. Rather than returning a single
/// > bit for each button in the group, an array returns an
/// > index in each field that corresponds to the pressed
/// > button
#[derive(Clone, Debug)]
pub struct ArrayField {
    pub report_id: Option<ReportId>,
    pub direction: Direction,
    pub bits: RangeInclusive<usize>,
    usages: Vec<Usage>,
    pub logical_range: LogicalRange,
    pub physical_range: Option<PhysicalRange>,
    pub unit: Option<Unit>,
    pub unit_exponent: Option<UnitExponent>,
    pub collections: Vec<Collection>,
}

impl ArrayField {
    pub fn usages(&self) -> &[Usage] {
        &self.usages
    }
}

/// A [ConstantField] is one that represents a [hid::MainItem]
/// with Constant data, see Section 6.2.2.4.
///
/// > Constant indicates the item is a static read-only field in a
/// > report and cannot be modified (written) by the
/// > host.
///
/// Data in a [ConstantField] should be ignored by the caller, it
/// is merely used as padding, usually to align the subsequent
/// value on a byte boundary.
#[derive(Clone, Debug)]
pub struct ConstantField {
    pub report_id: Option<ReportId>,
    pub direction: Direction,
    pub bits: RangeInclusive<usize>,
    usages: Vec<Usage>,
}

impl ConstantField {
    pub fn usages(&self) -> &[Usage] {
        &self.usages
    }
}

#[derive(Copy, Clone, Debug)]
pub struct Collection(u8);

#[derive(Error, Debug)]
pub enum ParserError {
    #[error("Invalid data {data} at offset {offset}: {message}")]
    InvalidData {
        offset: u32,
        data: u32,
        message: String,
    },
    #[error("Parsing would lead to out-of-bounds")]
    OutOfBounds,
}

type Result<T> = std::result::Result<T, ParserError>;

#[derive(Clone, Copy, Debug, Default)]
struct Globals {
    usage_page: Option<UsagePage>,
    logical_minimum: Option<LogicalMinimum>,
    logical_maximum: Option<LogicalMaximum>,
    physical_minimum: Option<PhysicalMinimum>,
    physical_maximum: Option<PhysicalMaximum>,
    unit_exponent: Option<UnitExponent>,
    unit: Option<Unit>,
    report_size: Option<ReportSize>,
    report_id: Option<ReportId>,
    report_count: Option<ReportCount>,
}

/// Special struct for the [Locals] because the usage_page
/// is optional for those, unlike our [Usage] struct which is
/// the finalized one.
#[derive(Clone, Copy, Debug)]
struct LocalUsage {
    usage_page: Option<UsagePage>,
    usage_id: UsageId,
}

#[derive(Clone, Debug, Default)]
struct Locals {
    usage: Vec<LocalUsage>,
    // FIXME: needs the same LocalUsage treatment
    usage_minimum: Option<UsageMinimum>,
    usage_maximum: Option<UsageMaximum>,
    designator_index: Option<DesignatorIndex>,
    designator_minimum: Option<DesignatorMinimum>,
    designator_maximum: Option<DesignatorMaximum>,
    string_index: Option<StringIndex>,
    string_minimum: Option<StringMinimum>,
    string_maximum: Option<StringMaximum>,
    delimiter: Option<Delimiter>,
}

#[derive(Debug)]
struct Stack {
    globals: Vec<Globals>,
    locals: Vec<Locals>,
    pub collections: Vec<Collection>,
}

impl Stack {
    fn new() -> Self {
        Stack {
            globals: vec![Globals::default()],
            locals: vec![Locals::default()],
            collections: vec![],
        }
    }

    fn push(&mut self) {
        let current = self.globals.last().unwrap();
        self.globals.push(*current);

        // FIXME: this clones the Usage vector which is likely to mess us up, I don't
        // think they transfer across push/pop
        let current = self.locals.last().unwrap().clone();
        self.locals.push(current);
    }

    fn pop(&mut self) {
        self.globals.pop();
        self.locals.pop();
    }

    fn reset_locals(&mut self) {
        self.locals = vec![Locals::default()];
    }

    fn globals(&mut self) -> &mut Globals {
        self.globals.last_mut().unwrap()
    }

    fn locals(&mut self) -> &mut Locals {
        self.locals.last_mut().unwrap()
    }

    // Should be globals and globals_mut but i'd have to
    // update the update_stack macro for that.
    fn globals_const(&self) -> &Globals {
        self.globals.last().unwrap()
    }

    fn locals_const(&self) -> &Locals {
        self.locals.last().unwrap()
    }
}

fn compile_usages(globals: &Globals, locals: &Locals) -> Vec<Usage> {
    // Prefer UsageMinimum/Maximum over Usage because the latter may be set from an earlier call
    match locals.usage_minimum {
        Some(_) => {
            let min: u32 = locals
                .usage_minimum
                .expect("Missing UsageMinimum in locals")
                .into();
            let max: u32 = locals
                .usage_maximum
                .expect("Missing UsageMaximum in locals")
                .into();
            let usage_page = globals.usage_page.expect("Missing UsagePage in globals");

            RangeInclusive::new(min, max)
                .map(|u| Usage {
                    usage_page: UsagePage(usage_page.into()),
                    usage_id: UsageId(u as u16),
                })
                .collect()
        }
        None => {
            if locals.usage.is_empty() {
                panic!("Missing Usage in locals");
            }
            locals
                .usage
                .iter()
                .map(|usage| match usage {
                    // local item's Usage had a Usage Page included
                    LocalUsage {
                        usage_page: Some(up),
                        usage_id,
                    } => Usage {
                        usage_page: *up,
                        usage_id: *usage_id,
                    },
                    // Usage Page comes from the global item
                    LocalUsage {
                        usage_page: None,
                        usage_id,
                    } => {
                        let usage_page = globals.usage_page.expect("Missing UsagePage in globals");
                        Usage {
                            usage_page,
                            usage_id: *usage_id,
                        }
                    }
                })
                .collect()
        }
    }
}

fn handle_main_item(
    item: &MainItem,
    stack: &mut Stack,
    rdesc: &mut ReportDescriptor,
) -> Result<Vec<Field>> {
    let globals = stack.globals_const();
    let locals = stack.locals_const();

    let direction = match item {
        MainItem::Input(i) => Direction::Input,
        MainItem::Output(i) => Direction::Output,
        MainItem::Feature(i) => Direction::Feature,
        _ => panic!("Invalid item for handle_main_item()"),
    };

    let report_id = globals.report_id;

    let (is_constant, is_variable) = match item {
        MainItem::Input(i) => (i.is_constant, i.is_variable),
        MainItem::Output(i) => (i.is_constant, i.is_variable),
        MainItem::Feature(i) => (i.is_constant, i.is_variable),
        _ => panic!("Invalid item for handle_main_item()"),
    };

    let bit_offset = 0;
    let report_size = globals.report_size.expect("Missing report size in globals");
    let report_count = globals
        .report_count
        .expect("Missing report count in globals");

    if is_constant {
        let nbits = usize::from(report_size) * usize::from(report_count);
        let bits = RangeInclusive::new(bit_offset, bit_offset + nbits - 1);

        let field = ConstantField {
            bits,
            report_id,
            direction,
            usages: vec![],
        };
        return Ok(vec![Field::Constant(field)]);
    }

    let logical_range = LogicalRange {
        minimum: globals.logical_minimum.expect("Missing LogicalMinimum"),
        maximum: globals.logical_maximum.expect("Missing LogicalMaximum"),
    };

    let physical_range = match (globals.physical_minimum, globals.physical_maximum) {
        (Some(min), Some(max)) => Some(PhysicalRange {
            minimum: globals.physical_minimum.unwrap(),
            maximum: globals.physical_maximum.unwrap(),
        }),
        _ => None,
    };

    let unit = globals.unit;
    let unit_exponent = globals.unit_exponent;

    let usages = compile_usages(globals, locals);
    let collections = stack.collections.clone();
    let fields: Vec<Field> = if is_variable {
        let mut bit_offset = 0;
        Range {
            start: 0,
            end: usize::from(report_count),
        }
        .map(|c| {
            let nbits = usize::from(report_size);
            let bits = RangeInclusive::new(bit_offset, bit_offset + nbits - 1);
            bit_offset += nbits;

            let usage = usages.get(c).or_else(|| usages.last()).unwrap();
            let field = VariableField {
                usages: vec![*usage],
                bits,
                logical_range,
                physical_range,
                unit,
                unit_exponent,
                collections: collections.clone(),
                report_id,
                direction,
            };
            Field::Variable(field)
        })
        .collect()
    } else {
        let bit_offset = 0;
        let nbits = usize::from(report_size) * usize::from(report_count);
        let bits = RangeInclusive::new(bit_offset, bit_offset + nbits - 1);

        let field = ArrayField {
            usages,
            bits,
            logical_range,
            physical_range,
            unit,
            unit_exponent,
            collections,
            report_id,
            direction,
        };

        vec![Field::Array(field)]
    };

    Ok(fields)
}

macro_rules! update_stack {
    ($stack:ident, $class:ident, $which:ident, $from:ident) => {
        //println!("Updating {} with value {:?}", stringify!($which), &$from);
        let state = $stack.$class();
        state.$which = Some($from);
    };
}

fn parse_report_descriptor(bytes: &[u8]) -> Result<ReportDescriptor> {
    let items = hid::ReportDescriptorItems::try_from(bytes)?;

    let mut stack = Stack::new();
    let mut rdesc = ReportDescriptor::default();

    for rdesc_item in items.iter() {
        let item = rdesc_item.item();
        match item.item_type() {
            ItemType::Main(MainItem::Collection(i)) => {
                let c = Collection(u8::from(&i));
                stack.collections.push(c);
            }
            ItemType::Main(MainItem::EndCollection) => {
                stack.collections.pop();
            }
            ItemType::Main(item) => {
                let mut fields = handle_main_item(&item, &mut stack, &mut rdesc)
                    .expect("main item parsing failed");
                stack.reset_locals();

                // Now update the returned field(s) and push them into the right report
                let direction = match item {
                    MainItem::Input(i) => Direction::Input,
                    MainItem::Output(i) => Direction::Output,
                    MainItem::Feature(i) => Direction::Feature,
                    _ => panic!("Invalid item for handle_main_item()"),
                };

                let reports: &mut Vec<RDescReport> = match direction {
                    Direction::Input => &mut rdesc.input_reports,
                    Direction::Output => &mut rdesc.output_reports,
                    Direction::Feature => &mut rdesc.feature_reports,
                };

                let report_id = fields.first().unwrap().report_id();
                let report = match report_id {
                    None => reports.first_mut(),
                    Some(id) => reports.iter_mut().find(|r| &r.id.unwrap() == id),
                };

                let report = match report {
                    None => {
                        let initial_size = if report_id.is_some() { 8 } else { 0 };
                        reports.push(RDescReport {
                            id: *report_id,
                            size: initial_size,
                            fields: vec![],
                        });
                        reports.last_mut().unwrap()
                    }
                    Some(r) => r,
                };

                // We know which report the fields belong to, let's update the offsets
                let offset = report.size;
                fields.iter_mut().for_each(|f| {
                    f.update_bit_offset(offset);
                    report.size += f.len();
                });

                report.fields.append(&mut fields);
            }
            ItemType::Long => {}
            ItemType::Reserved => {}
            ItemType::Global(GlobalItem::UsagePage { usage_page }) => {
                update_stack!(stack, globals, usage_page, usage_page);
            }
            ItemType::Global(GlobalItem::LogicalMinimum { minimum }) => {
                update_stack!(stack, globals, logical_minimum, minimum);
            }
            ItemType::Global(GlobalItem::LogicalMaximum { maximum }) => {
                update_stack!(stack, globals, logical_maximum, maximum);
            }
            ItemType::Global(GlobalItem::PhysicalMinimum { minimum }) => {
                update_stack!(stack, globals, physical_minimum, minimum);
            }
            ItemType::Global(GlobalItem::PhysicalMaximum { maximum }) => {
                update_stack!(stack, globals, physical_maximum, maximum);
            }
            ItemType::Global(GlobalItem::UnitExponent { exponent }) => {
                update_stack!(stack, globals, unit_exponent, exponent);
            }
            ItemType::Global(GlobalItem::Unit { unit }) => {
                update_stack!(stack, globals, unit, unit);
            }
            ItemType::Global(GlobalItem::ReportSize { size }) => {
                update_stack!(stack, globals, report_size, size);
            }
            ItemType::Global(GlobalItem::ReportId { id }) => {
                update_stack!(stack, globals, report_id, id);
            }
            ItemType::Global(GlobalItem::ReportCount { count }) => {
                update_stack!(stack, globals, report_count, count);
            }
            ItemType::Global(GlobalItem::Push) => {
                stack.push();
            }
            ItemType::Global(GlobalItem::Pop) => {
                stack.pop();
            }
            ItemType::Global(GlobalItem::Reserved) => {}
            ItemType::Local(LocalItem::Usage {
                usage_page,
                usage_id,
            }) => {
                let usage = LocalUsage {
                    usage_page,
                    usage_id,
                };
                stack.locals().usage.push(usage);
            }
            ItemType::Local(LocalItem::UsageMinimum { minimum }) => {
                update_stack!(stack, locals, usage_minimum, minimum);
            }
            ItemType::Local(LocalItem::UsageMaximum { maximum }) => {
                update_stack!(stack, locals, usage_maximum, maximum);
            }
            ItemType::Local(LocalItem::DesignatorIndex { index }) => {
                update_stack!(stack, locals, designator_index, index);
            }
            ItemType::Local(LocalItem::DesignatorMinimum { minimum }) => {
                update_stack!(stack, locals, designator_minimum, minimum);
            }
            ItemType::Local(LocalItem::DesignatorMaximum { maximum }) => {
                update_stack!(stack, locals, designator_maximum, maximum);
            }
            ItemType::Local(LocalItem::StringIndex { index }) => {
                update_stack!(stack, locals, string_index, index);
            }
            ItemType::Local(LocalItem::StringMinimum { minimum }) => {
                update_stack!(stack, locals, string_minimum, minimum);
            }
            ItemType::Local(LocalItem::StringMaximum { maximum }) => {
                update_stack!(stack, locals, string_maximum, maximum);
            }
            ItemType::Local(LocalItem::Delimiter { delimiter }) => {
                update_stack!(stack, locals, delimiter, delimiter);
            }
            ItemType::Local(LocalItem::Reserved { value: u8 }) => {}
        };
    }

    Ok(rdesc)
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_twos_comp() {
        assert_eq!(5u8.twos_comp(3), -3);
        assert_eq!(5u8.twos_comp(4), 5);
        assert_eq!(0xffu8.twos_comp(8), -1);

        assert_eq!(5u16.twos_comp(3), -3);
        assert_eq!(5u16.twos_comp(4), 5);
        assert_eq!(0xffffu16.twos_comp(16), -1);

        assert_eq!(5u32.twos_comp(3), -3);
        assert_eq!(5u32.twos_comp(4), 5);
        assert_eq!(0xffffffffu32.twos_comp(32), -1);
    }

    #[test]
    fn test_range_length() {
        assert_eq!(1, RangeInclusive::new(0usize, 0usize).len());
        assert_eq!(2, RangeInclusive::new(0usize, 1usize).len());
        assert_eq!(10, RangeInclusive::new(0usize, 9usize).len());
    }

    #[test]
    fn extract() {
        let bytes: [u8; 4] = [0b1100_1010, 0b1011_1001, 0b10010110, 0b00010101];

        assert_eq!(
            0,
            RDescReport::extract_u8(&bytes, &RangeInclusive::new(0, 0))
        );
        assert_eq!(
            2,
            RDescReport::extract_u8(&bytes, &RangeInclusive::new(0, 1))
        );
        assert_eq!(
            10,
            RDescReport::extract_u8(&bytes, &RangeInclusive::new(0, 3))
        );

        assert_eq!(
            0,
            RDescReport::extract_i8(&bytes, &RangeInclusive::new(0, 0))
        );
        assert_eq!(
            -2,
            RDescReport::extract_i8(&bytes, &RangeInclusive::new(0, 1))
        );
        assert_eq!(
            -6,
            RDescReport::extract_i8(&bytes, &RangeInclusive::new(0, 3))
        );

        assert_eq!(
            0b1001_1100,
            RDescReport::extract_u8(&bytes, &RangeInclusive::new(4, 11))
        );
        assert_eq!(
            0b1001_1100u8 as i8,
            RDescReport::extract_i8(&bytes, &RangeInclusive::new(4, 11))
        );

        assert_eq!(
            0,
            RDescReport::extract_u16(&bytes, &RangeInclusive::new(0, 0))
        );
        assert_eq!(
            2,
            RDescReport::extract_u16(&bytes, &RangeInclusive::new(0, 1))
        );
        assert_eq!(
            10,
            RDescReport::extract_u16(&bytes, &RangeInclusive::new(0, 3))
        );

        assert_eq!(
            0,
            RDescReport::extract_i16(&bytes, &RangeInclusive::new(0, 0))
        );
        assert_eq!(
            -2,
            RDescReport::extract_i16(&bytes, &RangeInclusive::new(0, 1))
        );
        assert_eq!(
            -6,
            RDescReport::extract_i16(&bytes, &RangeInclusive::new(0, 3))
        );

        assert_eq!(
            0b0110_1011_1001_1100,
            RDescReport::extract_u16(&bytes, &RangeInclusive::new(4, 19))
        );
        assert_eq!(
            0b0110_1011_1001_1100,
            RDescReport::extract_i16(&bytes, &RangeInclusive::new(4, 19))
        );
        assert_eq!(
            0b1_0110_1011_1001_110u16 as i16,
            RDescReport::extract_i16(&bytes, &RangeInclusive::new(5, 20))
        );

        assert_eq!(
            0b0110_1011_1001_1100,
            RDescReport::extract_u32(&bytes, &RangeInclusive::new(4, 19))
        );
        assert_eq!(
            0b0110_1011_1001_1100,
            RDescReport::extract_i32(&bytes, &RangeInclusive::new(4, 19))
        );
        assert_eq!(
            ((0b1_0110_1011_1001_110u16 as i16) as i32),
            RDescReport::extract_i32(&bytes, &RangeInclusive::new(5, 20))
        );

        assert_eq!(
            ((0b1_0110_1011_1001_110u16 as i16) as i32),
            RDescReport::extract_i32(&bytes, &RangeInclusive::new(5, 20))
        );
    }

    #[test]
    fn report_values() {
        let rv = ReportValue::Unsigned(0);
        assert_eq!(u32::from(&rv), 0);
        assert_eq!(i32::from(&rv), 0);
        assert_eq!(u16::from(&rv), 0);
        assert_eq!(i16::from(&rv), 0);
        assert_eq!(u8::from(&rv), 0);
        assert_eq!(i8::from(&rv), 0);

        assert_eq!(format!("{rv}"), "0");

        let rv = ReportValue::Unsigned(10);
        assert_eq!(u32::from(&rv), 10);
        assert_eq!(i32::from(&rv), 10);
        assert_eq!(u16::from(&rv), 10);
        assert_eq!(i16::from(&rv), 10);
        assert_eq!(u8::from(&rv), 10);
        assert_eq!(i8::from(&rv), 10);

        assert_eq!(format!("{rv}"), "10");
        assert_eq!(format!("{rv:x}"), "a");

        let rv = ReportValue::Signed(-10);
        assert_eq!(u32::from(&rv), 0xfffffff6);
        assert_eq!(i32::from(&rv), -10);
        assert_eq!(u16::from(&rv), 0xfff6);
        assert_eq!(i16::from(&rv), -10);
        assert_eq!(u8::from(&rv), 0xf6);
        assert_eq!(i8::from(&rv), -10);

        assert_eq!(format!("{rv}"), "-10");
        assert_eq!(format!("{rv:x}"), "fffffff6");

        let rv = ReportValue::Unsigned(257);
        assert_eq!(u32::from(&rv), 257);
        assert_eq!(i32::from(&rv), 257);
        assert_eq!(u16::from(&rv), 257);
        assert_eq!(i16::from(&rv), 257);
        assert_eq!(u8::from(&rv), 1);
        assert_eq!(i8::from(&rv), 1);

        assert_eq!(format!("{rv}"), "257");
        assert_eq!(format!("{rv:x}"), "101");

        let rv = ReportValue::Signed(-257i32);
        assert_eq!(u32::from(&rv), 0xfffffeff);
        assert_eq!(i32::from(&rv), -257);
        assert_eq!(u16::from(&rv), 0xfeff);
        assert_eq!(i16::from(&rv), -257);
        assert_eq!(u8::from(&rv), 0xff);
        assert_eq!(i8::from(&rv), -1);

        assert_eq!(format!("{rv}"), "-257");
        assert_eq!(format!("{rv:x}"), "fffffeff");
    }
}
