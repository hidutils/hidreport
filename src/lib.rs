// SPDX-License-Identifier: MIT
//
//! This crate provides parsing of HID Report Descriptors, including the [hid] module to inspect
//! a report descriptor in more detail and the [hut] module for known HID Usages.
//!
//! Entry point is usually [`ReportDescriptor::try_from(bytes)`](ReportDescriptor::try_from):
//!
//! ```
//! # use hidreport::*;
//! # let bytes: &[u8] = &[0x05, 0x01, 0x09, 0x02, 0xa1, 0x01, 0x05, 0x01, 0x09, 0x02, 0xa1, 0x02, 0x85, 0x1a, 0x09, 0x01, 0xa1, 0x00, 0x05, 0x09, 0x19, 0x01, 0x29, 0x05, 0x95, 0x05, 0x75, 0x01, 0x15, 0x00, 0x25, 0x01, 0x81, 0x02, 0x75, 0x03, 0x95, 0x01, 0x81, 0x01, 0x05, 0x01, 0x09, 0x30, 0x09, 0x31, 0x95, 0x02, 0x75, 0x10, 0x16, 0x01, 0x80, 0x26, 0xff, 0x7f, 0x81, 0x06, 0xa1, 0x02, 0x85, 0x12, 0x09, 0x48, 0x95, 0x01, 0x75, 0x02, 0x15, 0x00, 0x25, 0x01, 0x35, 0x01, 0x45, 0x0c, 0xb1, 0x02, 0x85, 0x1a, 0x09, 0x38, 0x35, 0x00, 0x45, 0x00, 0x95, 0x01, 0x75, 0x10, 0x16, 0x01, 0x80, 0x26, 0xff, 0x7f, 0x81, 0x06, 0xc0, 0xa1, 0x02, 0x85, 0x12, 0x09, 0x48, 0x75, 0x02, 0x15, 0x00, 0x25, 0x01, 0x35, 0x01, 0x45, 0x0c, 0xb1, 0x02, 0x35, 0x00, 0x45, 0x00, 0x75, 0x04, 0xb1, 0x01, 0x85, 0x1a, 0x05, 0x0c, 0x95, 0x01, 0x75, 0x10, 0x16, 0x01, 0x80, 0x26, 0xff, 0x7f, 0x0a, 0x38, 0x02, 0x81, 0x06, 0xc0, 0xc0, 0xc0, 0xc0, 0x05, 0x0c, 0x09, 0x01, 0xa1, 0x01, 0x05, 0x01, 0x09, 0x02, 0xa1, 0x02, 0x85, 0x1f, 0x05, 0x0c, 0x0a, 0x38, 0x02, 0x95, 0x01, 0x75, 0x10, 0x16, 0x01, 0x80, 0x26, 0xff, 0x7f, 0x81, 0x06, 0x85, 0x17, 0x06, 0x00, 0xff, 0x0a, 0x06, 0xff, 0x0a, 0x0f, 0xff, 0x15, 0x00, 0x25, 0x01, 0x35, 0x01, 0x45, 0x0c, 0x95, 0x02, 0x75, 0x02, 0xb1, 0x02, 0x0a, 0x04, 0xff, 0x35, 0x00, 0x45, 0x00, 0x95, 0x01, 0x75, 0x01, 0xb1, 0x02, 0x75, 0x03, 0xb1, 0x01, 0xc0, 0xc0];
//! # fn read_from_device() -> Vec<u8> {
//! #     vec![0x1a, 0x00, 0xff, 0xff, 0xfe, 0xff, 00, 00, 00, 0x00]
//! # }
//! #
//! let rdesc: ReportDescriptor = ReportDescriptor::try_from(bytes).unwrap();
//! for r in rdesc.input_reports() {
//!     println!("Input Report with report ID: {:?}", r.report_id());
//! }
//!
//! let input_report_bytes = read_from_device();
//! let report = rdesc.find_input_report(&input_report_bytes).unwrap();
//! println!("This is an input report for report ID: {:?}", report.report_id());
//! let field = report.fields().first().unwrap();
//! match field {
//!     Field::Variable(var) => {
//!         let val: u32 = var.extract_u32(&input_report_bytes).unwrap();
//!         println!("Field {:?} is of value {}", field, val);
//!     }
//!     Field::Array(arr) => {
//!         let vals: Vec<u32> = arr.extract_u32(&input_report_bytes).unwrap();
//!         println!("Field {:?} has values {:?}", field, vals);
//!     }
//!     Field::Constant(_) => {
//!         println!("Field {:?} is <padding data>", field);
//!     }
//! }
//! ```
//!
//! In this document and unless stated otherwise, a reference to "Section a.b.c" refers to the
//! [HID Device Class Definition for HID 1.11](https://www.usb.org/document-library/device-class-definition-hid-111).

use std::hash::{Hash, Hasher};
use std::ops::{Range, RangeInclusive};
use thiserror::Error;

pub mod hid;
pub mod hut;
pub mod types;

pub use hid::CollectionItem as CollectionType;
use hid::*;
pub use types::*;

macro_rules! ensure {
    ($cond:expr, $msg:literal) => {
        if (!$cond) {
            return Err(ParserError::InvalidData {
                offset: 0,
                message: $msg.into(),
            });
        }
    };
    ($cond:expr, $err:expr) => {
        if (!$cond) {
            return Err($err);
        }
    };
}
pub(crate) use ensure;

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
    let value: u64 = Range {
        start: 0u64,
        end: bytes.len() as u64,
    }
    //.inspect(|idx| println!("Accessing index {idx}: {:x?}", bytes[*idx as usize]))
    .fold(0u64, |acc: u64, idx| {
        acc | (bytes[idx as usize] as u64) << (8 * idx)
    });

    let base_shift = bits.start() % 8;
    let mask_shift = 32 - nbits;
    let mask = (!0) >> mask_shift;
    let value = (value >> base_shift) as u32;

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
    let v = extract_u32(bytes, bits);
    v.twos_comp(nbits)
}

fn extract_u16(bytes: &[u8], bits: &RangeInclusive<usize>) -> u16 {
    assert!(bits.len() <= 16);
    let v: u32 = extract_u32(bytes, bits);
    v as u16
}

fn extract_i16(bytes: &[u8], bits: &RangeInclusive<usize>) -> i16 {
    let nbits = bits.len();
    let v = extract_u16(bytes, bits);
    v.twos_comp(nbits)
}

fn extract_u8(bytes: &[u8], bits: &RangeInclusive<usize>) -> u8 {
    assert!(bits.len() <= 8);
    let v: u32 = extract_u32(bytes, bits);
    v as u8
}

fn extract_i8(bytes: &[u8], bits: &RangeInclusive<usize>) -> i8 {
    let nbits = bits.len();
    let v = extract_u8(bytes, bits);
    v.twos_comp(nbits)
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
/// # fn read_from_device() -> Vec<u8> {
/// #     vec![0x1a, 0x00, 0xff, 0xff, 0xfe, 0xff, 00, 00, 00, 0x00]
/// # }
/// #
/// let rdesc: ReportDescriptor = ReportDescriptor::try_from(bytes).unwrap();
/// for r in rdesc.input_reports() {
///     println!("Input Report with report ID: {:?}", r.report_id());
/// }
/// let input_report_bytes = read_from_device();
/// let report = rdesc.find_input_report(&input_report_bytes).unwrap();
/// println!("This is an input report for report ID: {:?}", report.report_id());
/// let field = report.fields().first().unwrap();
/// match field {
///     Field::Variable(var) => println!("Field {:?} is of value {}", field, var.extract_u32(&input_report_bytes).unwrap()),
///     Field::Array(arr) => println!("Field {:?} has values {:?}", field, arr.extract_u32(&input_report_bytes).unwrap()),
///     Field::Constant(_) => println!("Field {:?} is <padding data>", field),
/// }
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
    /// ```
    /// # use hidreport::*;
    /// # fn func(rdesc: &ReportDescriptor) {
    /// let reports = rdesc.input_reports();
    /// for report in reports {
    ///     println!("Report ID: {:?}", report.report_id());
    /// }
    /// # }
    /// ```
    pub fn input_reports(&self) -> &[impl Report] {
        &self.input_reports
    }

    /// Returns the set of output reports or the empty
    /// slice if none exist.
    /// ```
    /// # use hidreport::*;
    /// # fn func(rdesc: &ReportDescriptor) {
    /// let reports = rdesc.output_reports();
    /// for report in reports {
    ///     println!("Report ID: {:?}", report.report_id());
    /// }
    /// # }
    /// ```
    pub fn output_reports(&self) -> &[impl Report] {
        &self.output_reports
    }

    /// Returns the set of feature reports or the empty
    /// slice if none exist.
    /// ```
    /// # use hidreport::*;
    /// # fn func(rdesc: &ReportDescriptor) {
    /// let reports = rdesc.feature_reports();
    /// for report in reports {
    ///     println!("Report ID: {:?}", report.report_id());
    /// }
    /// # }
    /// ```
    pub fn feature_reports(&self) -> &[impl Report] {
        &self.feature_reports
    }

    fn find_report(&'a self, list: &'a [RDescReport], prefix: u8) -> Option<&impl Report> {
        let first = list.first()?;
        let rid = Some(ReportId(prefix));
        // Do we have report IDs? If not, the first report is what we want.
        match first.report_id() {
            None => Some(first),
            Some(_) => list.iter().find(|r| r.report_id() == &rid),
        }
    }

    /// Find the input report that matches this byte sequence.
    ///
    /// ```
    /// # use hidreport::*;
    /// # fn func(bytes: &[u8], rdesc: &ReportDescriptor) {
    /// // bytes was read from the device (or some other source)
    /// let report = rdesc.find_input_report(bytes).unwrap();
    /// for field in report.fields() {
    ///     // ...
    /// }
    /// # }
    /// ```
    ///
    /// ReportDescriptors with multiple reports require a report
    /// to have a single byte prefix specifying the [ReportId].
    pub fn find_input_report(&self, bytes: &[u8]) -> Option<&impl Report> {
        self.find_report(&self.input_reports, bytes[0])
    }

    /// Find the output report that matches this byte sequence.
    ///
    /// ```
    /// # use hidreport::*;
    /// # fn func(bytes: &[u8], rdesc: &ReportDescriptor) {
    /// // bytes was read from the device (or some other source)
    /// let report = rdesc.find_output_report(bytes).unwrap();
    /// for field in report.fields() {
    ///     // ...
    /// }
    /// # }
    /// ```
    ///
    /// ReportDescriptors with multiple reports require a report
    /// to have a single byte prefix specifying the [ReportId].
    pub fn find_output_report(&self, bytes: &[u8]) -> Option<&impl Report> {
        self.find_report(&self.input_reports, bytes[0])
    }

    /// Find the feature report that matches this byte sequence.
    ///
    /// ```
    /// # use hidreport::*;
    /// # fn func(bytes: &[u8], rdesc: &ReportDescriptor) {
    /// // bytes was read from the device (or some other source)
    /// let report = rdesc.find_feature_report(bytes).unwrap();
    /// for field in report.fields() {
    ///     // ...
    /// }
    /// # }
    /// ```
    ///
    /// ReportDescriptors with multiple reports require a report
    /// to have a single byte prefix specifying the [ReportId].
    pub fn find_feature_report(&self, bytes: &[u8]) -> Option<&impl Report> {
        self.find_report(&self.input_reports, bytes[0])
    }
}

impl TryFrom<&[u8]> for ReportDescriptor {
    type Error = ParserError;

    /// Try to parse the given byte array as a report descriptor.
    fn try_from(bytes: &[u8]) -> Result<ReportDescriptor> {
        parse_report_descriptor(bytes)
    }
}

#[derive(Copy, Clone, Debug)]
enum Direction {
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
/// Use [`size_in_bits()`][Report::size_in_bits] or
/// [`size_in_bytes()`](Report::size_in_bytes) to
/// get the length of this report.
///
/// Note that each of Input, Output and Feature Reports
/// have their own enumeration of Report IDs, i.e. an Input Report
/// with a Report ID of e.g. 1 may have a different size and/or [Field]s
/// to an Output Report with a Report ID of 1.
///
/// The Report ID has no meaning other than to distinguish
/// different reports. See Section 6.2.2.7 for details.
pub trait Report {
    /// Returns the HID Report ID for this report, if any.
    fn report_id(&self) -> &Option<ReportId>;

    /// Returns the parsed HID Fields ID for this report. A caller should
    /// iterate through these fields to find the ones it is interested
    /// in and use the [Field::bits] to extract the data from future
    /// reports.
    fn fields(&self) -> &[Field];

    /// The size in bits for this report.
    fn size_in_bits(&self) -> usize;

    /// The size in bytes for this object.
    ///
    /// Where [`size_in_bits()`](Report::size_in_bits) is
    /// not a multiple of 8, the [`size_in_bytes()`](Report::size_in_bytes) rounds up
    /// fit all bits.
    fn size_in_bytes(&self) -> usize {
        (self.size_in_bits() + 7) / 8
    }
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

    /// The size of this HID report on the wire, in bits
    fn size_in_bits(&self) -> usize {
        self.size
    }
}

/// The usage of a [Field] defines the interpretation of a
/// data value. See the [hut] module for a list of known Usages.
///
/// A Usage comprises of a 16 bit [UsagePage] and a 16 bit [UsageId].
///
/// ```
/// # use hidreport::*;
/// let up = UsagePage::from(0x01); // Generic Desktop
/// let uid = UsageId::from(0x02); // Mouse
/// let usage = Usage::from_page_and_id(up, uid);
/// ```
/// For known named usages see [hut::Usage].
#[derive(Clone, Copy, Debug, PartialEq)]
pub struct Usage {
    pub usage_page: UsagePage,
    pub usage_id: UsageId,
}

impl Usage {
    /// Create a [Usage] from a [UsagePage] and a [UsageId].
    pub fn from_page_and_id(usage_page: UsagePage, usage_id: UsageId) -> Usage {
        Usage {
            usage_page,
            usage_id,
        }
    }
}

impl From<u32> for Usage {
    fn from(u: u32) -> Usage {
        Usage {
            usage_page: UsagePage::from((u >> 16) as u16),
            usage_id: UsageId::from((u & 0xffff) as u16),
        }
    }
}

impl From<&Usage> for u32 {
    fn from(u: &Usage) -> u32 {
        (u16::from(u.usage_page) as u32) << 16 | u16::from(u.usage_id) as u32
    }
}

impl_from_without_ref!(Usage, u32, u32);

impl From<&Usage> for UsageMinimum {
    fn from(u: &Usage) -> UsageMinimum {
        UsageMinimum(u32::from(u))
    }
}

impl_from_without_ref!(Usage, UsageMinimum, UsageMinimum);

impl From<&Usage> for UsageMaximum {
    fn from(u: &Usage) -> UsageMaximum {
        UsageMaximum(u32::from(u))
    }
}

impl_from_without_ref!(Usage, UsageMaximum, UsageMaximum);

/// A unique (within this report descriptor) identifier for a [Field].
#[derive(Clone, Copy, Debug, PartialEq, Hash, PartialOrd)]
pub struct FieldId(u32);

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
    pub fn id(&self) -> FieldId {
        match self {
            Field::Variable(f) => f.id,
            Field::Array(f) => f.id,
            Field::Constant(f) => f.id,
        }
    }
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

    /// The length of the field in bits
    fn len(&self) -> usize {
        return self.bits().len();
    }

    pub fn collections(&self) -> &[Collection] {
        match self {
            Field::Variable(f) => &f.collections,
            Field::Array(f) => &f.collections,
            Field::Constant(..) => &[],
        }
    }
}

/// A [VariableField] represents a single physical control.
#[derive(Clone, Debug)]
pub struct VariableField {
    id: FieldId,
    report_id: Option<ReportId>,
    pub bits: RangeInclusive<usize>,
    pub usage: Usage,
    pub logical_minimum: LogicalMinimum,
    pub logical_maximum: LogicalMaximum,
    pub physical_minimum: Option<PhysicalMinimum>,
    pub physical_maximum: Option<PhysicalMaximum>,
    pub unit: Option<Unit>,
    pub unit_exponent: Option<UnitExponent>,
    pub collections: Vec<Collection>,
}

impl VariableField {
    /// Returns true if this field contains signed values,
    /// i.e. the LogicalMinimum is less than zero.
    pub fn is_signed(&self) -> bool {
        self.logical_minimum < LogicalMinimum(0)
    }

    /// Extract this field's value as [u32] from a report's bytes.
    /// The value is extracted as its correct bit size but upcasted
    /// if need be into a [u32]. IOW it is safe to call this function
    /// on e.g. an 8 bit unsigned field in the report.
    ///
    /// Check [VariableField::is_signed] first to see if you should be
    /// using [VariableField::extract_i32] instead.
    pub fn extract_u32(&self, bytes: &[u8]) -> Result<u32> {
        if let Some(report_id) = self.report_id {
            if ReportId(bytes[0]) != report_id {
                return Err(ParserError::MismatchingReportId);
            }
        }

        let v = match self.bits.len() {
            1..=8 => extract_u8(bytes, &self.bits) as u32,
            9..=16 => extract_u16(bytes, &self.bits) as u32,
            17..=32 => extract_u32(bytes, &self.bits),
            n => panic!("invalid data length {n}"),
        };

        Ok(v)
    }

    /// Extract this field's value as [i32] from a report's bytes.
    /// The value is extracted as its correct bit size but upcasted
    /// if need be into a [i32]. IOW it is safe to call this function
    /// on e.g. an 8 bit signed field in the report.
    ///
    /// Check [VariableField::is_signed] first to see if you should be
    /// using [VariableField::extract_u32] instead.
    pub fn extract_i32(&self, bytes: &[u8]) -> Result<i32> {
        if let Some(report_id) = self.report_id {
            if ReportId(bytes[0]) != report_id {
                return Err(ParserError::MismatchingReportId);
            }
        }

        let v = match self.bits.len() {
            1..=8 => extract_i8(bytes, &self.bits) as i32,
            9..=16 => extract_i16(bytes, &self.bits) as i32,
            17..=32 => extract_i32(bytes, &self.bits),
            n => panic!("invalid data length {n}"),
        };

        Ok(v)
    }
}

/// Wrapper around the commonly used [UsageMinimum] and [UsageMaximum].
#[derive(Debug)]
pub struct UsageRange {
    usage_page: UsagePage,
    minimum: UsageMinimum,
    maximum: UsageMaximum,
}

impl UsageRange {
    /// The [UsageMinimum]. Note that in reports and report descriptors
    /// the Usage Minimum may or may not include the Usage Page. The
    /// minimum returned here always includes the [UsagePage].
    pub fn minimum(&self) -> UsageMinimum {
        self.minimum
    }

    /// The [UsageMaximum]. Note that in reports and report descriptors
    /// the Usage Maximum may or may not include the Usage Page. The
    /// maximum returned here always includes the [UsagePage].
    pub fn maximum(&self) -> UsageMaximum {
        self.maximum
    }

    /// If the given usage falls within this usage range (i.e. it is of the
    /// same [UsagePage] and it within the inclusive [UsageMinimum]/[UsageMaximum])
    /// return the provided usage as [Option].
    pub fn lookup_usage<'a>(&self, usage: &'a Usage) -> Option<&'a Usage> {
        if usage.usage_page == self.usage_page
            && usage.usage_id >= self.minimum.usage_id()
            && usage.usage_id <= self.maximum.usage_id()
        {
            Some(usage)
        } else {
            None
        }
    }

    /// Look up the given [UsageId] and return the corresponding
    /// [Usage], if any. The [UsageId] is assumed to be in the same
    /// [UsagePage] as this range, use [lookup_usage()][Self::lookup_usage] if you need
    /// a check for the [UsagePage] as well.
    pub fn lookup_id(&self, id: UsageId) -> Option<Usage> {
        if id >= self.minimum.usage_id() && id <= self.maximum.usage_id() {
            Some(Usage::from_page_and_id(self.usage_page, id))
        } else {
            None
        }
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
    id: FieldId,
    report_id: Option<ReportId>,
    pub bits: RangeInclusive<usize>,
    usages: Vec<Usage>,
    pub report_count: ReportCount,
    pub logical_minimum: LogicalMinimum,
    pub logical_maximum: LogicalMaximum,
    pub physical_minimum: Option<PhysicalMinimum>,
    pub physical_maximum: Option<PhysicalMaximum>,
    pub unit: Option<Unit>,
    pub unit_exponent: Option<UnitExponent>,
    pub collections: Vec<Collection>,
}

impl ArrayField {
    /// Returns the set of usages for this field. This is the
    /// inclusive range of [UsageMinimum]`..=`[UsageMaximum]
    /// as defined for this field.
    ///
    /// In most cases it's better to use [usage_range()](Self::usage_range)
    /// instead.
    pub fn usages(&self) -> &[Usage] {
        &self.usages
    }

    /// Returns the [UsageRange] for this field.
    pub fn usage_range(&self) -> UsageRange {
        let min = self.usages.first().unwrap();
        let max = self.usages.last().unwrap();

        UsageRange {
            usage_page: min.usage_page,
            minimum: UsageMinimum::from(min),
            maximum: UsageMaximum::from(max),
        }
    }

    /// Returns true if this field contains signed values,.
    /// i.e. the LogicalMinimum is less than zero.
    /// ```
    /// # use hidreport::ArrayField;
    /// # fn func(field: &ArrayField, bytes: &[u8]) {
    /// if field.is_signed() {
    ///     println!("Signed values: {:?}", field.extract_i32(bytes).unwrap());
    /// } else {
    ///     println!("Unsigned values: {:?}", field.extract_u32(bytes).unwrap());
    /// }
    ///
    /// # }
    /// ```
    pub fn is_signed(&self) -> bool {
        self.logical_minimum < LogicalMinimum(0)
    }

    /// Extract this field's values as [u32]s from a report's bytes.
    /// The values are extracted at their correct bit size but upcasted
    /// if need be into a [u32]. IOW it is safe to call this function
    /// on e.g. an 8 bit unsigned field in the report.
    ///
    /// Check [ArrayField::is_signed] first to see if you should be
    /// using [ArrayField::extract_i32] instead.
    pub fn extract_u32(&self, bytes: &[u8]) -> Result<Vec<u32>> {
        if let Some(report_id) = self.report_id {
            if ReportId(bytes[0]) != report_id {
                return Err(ParserError::MismatchingReportId);
            }
        }
        let count = usize::from(self.report_count);
        let values: Result<Vec<u32>> = (0..count)
            .map(|idx| self.extract_one_u32(bytes, idx))
            .collect();

        values
    }

    /// Extract this field's values as [i32]s from a report's bytes.
    /// The values are extracted at their correct bit size but upcasted
    /// if need be into a [i32]. IOW it is safe to call this function
    /// on e.g. an 8 bit signed field in the report.
    ///
    /// Check [ArrayField::is_signed] first to see if you should be
    /// using [ArrayField::extract_u32] instead.
    pub fn extract_i32(&self, bytes: &[u8]) -> Result<Vec<i32>> {
        if let Some(report_id) = self.report_id {
            if ReportId(bytes[0]) != report_id {
                return Err(ParserError::MismatchingReportId);
            }
        }

        let count = usize::from(self.report_count);
        let values: Result<Vec<i32>> = (0..count)
            .map(|idx| self.extract_one_i32(bytes, idx))
            .collect();

        values
    }

    /// Extract a single value from this array. See [ArrayField::extract_u32].
    ///
    /// The index must be less than [Self::report_count].
    pub fn extract_one_u32(&self, bytes: &[u8], idx: usize) -> Result<u32> {
        if idx >= usize::from(self.report_count) {
            return Err(ParserError::OutOfBounds);
        }
        if let Some(report_id) = self.report_id {
            if ReportId(bytes[0]) != report_id {
                return Err(ParserError::MismatchingReportId);
            }
        }

        let count = usize::from(self.report_count);
        let bits_per_report = self.bits.len() / count;

        let offset = self.bits.start() + bits_per_report * idx;
        let bits = offset..=offset + bits_per_report - 1;
        let v = match bits.len() {
            1..=8 => extract_u8(bytes, &bits) as u32,
            9..=16 => extract_u16(bytes, &bits) as u32,
            17..=32 => extract_u32(bytes, &bits),
            n => panic!("invalid data length {n}"),
        };

        Ok(v)
    }

    /// Extract a single value from this array. See [ArrayField::extract_i32].
    ///
    /// The index must be less than [Self::report_count].
    pub fn extract_one_i32(&self, bytes: &[u8], idx: usize) -> Result<i32> {
        if idx >= usize::from(self.report_count) {
            return Err(ParserError::OutOfBounds);
        }
        if let Some(report_id) = self.report_id {
            if ReportId(bytes[0]) != report_id {
                return Err(ParserError::MismatchingReportId);
            }
        }

        let count = usize::from(self.report_count);
        let bits_per_report = self.bits.len() / count;

        let offset = self.bits.start() + bits_per_report * idx;
        let bits = offset..=offset + bits_per_report - 1;
        let v = match bits.len() {
            1..=8 => extract_i8(bytes, &bits) as i32,
            9..=16 => extract_i16(bytes, &bits) as i32,
            17..=32 => extract_i32(bytes, &bits),
            n => panic!("invalid data length {n}"),
        };

        Ok(v)
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
    id: FieldId,
    report_id: Option<ReportId>,
    pub bits: RangeInclusive<usize>,
    usages: Vec<Usage>,
}

impl ConstantField {
    pub fn usages(&self) -> &[Usage] {
        &self.usages
    }
}

/// A unique (within this report descriptor) identifier for a collection.
///
/// A device may have multiple collections that are otherwise identical
/// (in particular logical collections), the collection ID serves
/// to identify whether two fields are part of the same collection.
#[derive(Clone, Debug, PartialEq, Hash, PartialOrd)]
pub struct CollectionId(u32);

/// Collections group [Fields](Field) together into logical or physical
/// groups.
///
/// For example, a set of buttons and x/y axes may be grouped
/// together to represent a Mouse device.
/// Each [Field] may belong to a number of collections.
///
/// ```
/// # use hidreport::*;
/// # fn func(field: &VariableField) {
/// let collection = field.collections.first().unwrap();
/// match collection.collection_type() {
///     CollectionType::Physical => println!("This field is part of a physical collection"),
///     _ => {},
/// }
/// # }
/// ```
///
#[derive(Clone, Debug)]
pub struct Collection {
    id: CollectionId,
    collection_type: CollectionType,
    usages: Vec<Usage>,
}

impl Collection {
    /// Returns the unique ID for this collection
    pub fn id(&self) -> &CollectionId {
        &self.id
    }
    /// Return the type of this collection (e.g. physical, logical, ...)
    pub fn collection_type(&self) -> CollectionType {
        self.collection_type
    }

    /// Returns the usages assigned to this collection
    pub fn usages(&self) -> &[Usage] {
        &self.usages
    }
}

impl PartialEq for Collection {
    fn eq(&self, other: &Self) -> bool {
        self.id == other.id
    }
}

impl Eq for Collection {}

impl Hash for Collection {
    fn hash<H: Hasher>(&self, state: &mut H) {
        self.id.hash(state);
    }
}

#[derive(Error, Debug)]
pub enum ParserError {
    #[error("Invalid data at offset {offset}: {message}")]
    InvalidData { offset: usize, message: String },
    #[error("Parsing would lead to out-of-bounds")]
    OutOfBounds,
    #[error("Mismatching Report ID")]
    MismatchingReportId,
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

    fn pop(&mut self) -> Result<()> {
        ensure!(
            !self.globals.is_empty() && !self.locals.is_empty(),
            ParserError::InvalidData {
                offset: 0,
                message: "Too many Pops".into(),
            }
        );
        self.globals.pop();
        self.locals.pop();
        ensure!(
            !self.globals.is_empty() && !self.locals.is_empty(),
            ParserError::InvalidData {
                offset: 0,
                message: "Too many Pops, not enough Pushes".into(),
            }
        );
        Ok(())
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

fn compile_usages(globals: &Globals, locals: &Locals) -> Result<Vec<Usage>> {
    // Prefer UsageMinimum/Maximum over Usage because the latter may be set from an earlier call
    match locals.usage_minimum {
        Some(_) => {
            let Some(min) = locals.usage_minimum else {
                return Err(ParserError::InvalidData {
                    offset: 0,
                    message: "Missing UsageMinimum in locals".into(),
                });
            };
            let Some(max) = locals.usage_maximum else {
                return Err(ParserError::InvalidData {
                    offset: 0,
                    message: "Missing UsageMaximum in locals".into(),
                });
            };
            let Some(usage_page) = globals.usage_page else {
                return Err(ParserError::InvalidData {
                    offset: 0,
                    message: "Missing UsagePage in globals".into(),
                });
            };
            let min: u32 = min.into();
            let max: u32 = max.into();

            let usages = RangeInclusive::new(min, max)
                .map(|u| Usage {
                    usage_page: UsagePage(usage_page.into()),
                    usage_id: UsageId(u as u16),
                })
                .collect();
            Ok(usages)
        }
        None => {
            let usages = locals
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
                .collect();
            Ok(usages)
        }
    }
}

fn handle_main_item(item: &MainItem, stack: &mut Stack, base_id: u32) -> Result<Vec<Field>> {
    let globals = stack.globals_const();
    let locals = stack.locals_const();

    let report_id = globals.report_id;

    let (is_constant, is_variable) = match item {
        MainItem::Input(i) => (i.is_constant(), i.is_variable()),
        MainItem::Output(i) => (i.is_constant(), i.is_variable()),
        MainItem::Feature(i) => (i.is_constant(), i.is_variable()),
        _ => panic!("Invalid item for handle_main_item()"),
    };

    let bit_offset = 0;
    ensure!(
        globals.report_size.is_some(),
        "Missing report size in globals"
    );
    ensure!(
        globals.report_count.is_some(),
        "Missing report count in globals"
    );
    let report_size = globals.report_size.unwrap();
    let report_count = globals.report_count.unwrap();

    if is_constant {
        let nbits = usize::from(report_size) * usize::from(report_count);
        let bits = RangeInclusive::new(bit_offset, bit_offset + nbits - 1);

        let field = ConstantField {
            id: FieldId(base_id + bit_offset as u32),
            bits,
            report_id,
            usages: vec![],
        };
        return Ok(vec![Field::Constant(field)]);
    }

    ensure!(globals.logical_minimum.is_some(), "Missing LogicalMinimum");
    ensure!(globals.logical_maximum.is_some(), "Missing LogicalMaximum");
    let logical_minimum = globals.logical_minimum.unwrap();
    let logical_maximum = globals.logical_maximum.unwrap();

    ensure!(
        globals.physical_minimum.is_some() == globals.physical_maximum.is_some(),
        "Missing PhysicalMinimum or PhysicalMaximum"
    );
    let physical_minimum = globals.physical_minimum;
    let physical_maximum = globals.physical_maximum;

    let unit = globals.unit;
    let unit_exponent = globals.unit_exponent;

    let usages = compile_usages(globals, locals)?;
    ensure!(!usages.is_empty(), "Missing Usages for main item");

    // This may be an empty vec
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
                id: FieldId(base_id + bit_offset as u32),
                usage: *usage,
                bits,
                logical_minimum,
                logical_maximum,
                physical_minimum,
                physical_maximum,
                unit,
                unit_exponent,
                collections: collections.clone(),
                report_id,
            };
            Field::Variable(field)
        })
        .collect()
    } else {
        let bit_offset = 0;
        let nbits = usize::from(report_size) * usize::from(report_count);
        let bits = RangeInclusive::new(bit_offset, bit_offset + nbits - 1);

        let field = ArrayField {
            id: FieldId(base_id + bit_offset as u32),
            usages,
            bits,
            logical_minimum,
            logical_maximum,
            physical_minimum,
            physical_maximum,
            unit,
            unit_exponent,
            collections,
            report_id,
            report_count,
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
        //println!("Handling offset {}", rdesc_item.offset());
        let item = rdesc_item.item();
        match item.item_type() {
            ItemType::Main(MainItem::Collection(i)) => {
                let globals = stack.globals_const();
                let locals = stack.locals_const();
                // This may be an empty vec
                let usages = match compile_usages(globals, locals) {
                    Ok(usages) => usages,
                    Err(ParserError::InvalidData { message, .. }) => {
                        return Err(ParserError::InvalidData {
                            offset: rdesc_item.offset(),
                            message,
                        })
                    }
                    Err(e) => return Err(e),
                };
                let c = Collection {
                    id: CollectionId(rdesc_item.offset() as u32),
                    collection_type: i,
                    usages,
                };
                stack.collections.push(c);
                stack.reset_locals();
            }
            ItemType::Main(MainItem::EndCollection) => {
                if stack.collections.pop().is_none() {
                    return Err(ParserError::InvalidData {
                        offset: rdesc_item.offset(),
                        message: "Too many EndCollection".into(),
                    });
                };
                stack.reset_locals();
            }
            ItemType::Main(item) => {
                let mut fields =
                    match handle_main_item(&item, &mut stack, (rdesc_item.offset() * 8) as u32) {
                        Ok(fields) => fields,
                        Err(ParserError::InvalidData { message, .. }) => {
                            return Err(ParserError::InvalidData {
                                offset: rdesc_item.offset(),
                                message,
                            })
                        }
                        Err(e) => return Err(e),
                    };
                ensure!(
                    !fields.is_empty(),
                    ParserError::InvalidData {
                        offset: rdesc_item.offset(),
                        message: "Empty fields on MainItem".into(),
                    }
                );
                stack.reset_locals();

                // Now update the returned field(s) and push them into the right report
                let direction = match item {
                    MainItem::Input(_) => Direction::Input,
                    MainItem::Output(_) => Direction::Output,
                    MainItem::Feature(_) => Direction::Feature,
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
                    Some(id) => reports
                        .iter_mut()
                        .find(|r| r.id.is_some() && &r.id.unwrap() == id),
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

                // We know which report the fields belong to, let's update the offsets and field id
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
            ItemType::Global(GlobalItem::Pop) => match stack.pop() {
                Ok(_) => {}
                Err(ParserError::InvalidData { message, .. }) => {
                    return Err(ParserError::InvalidData {
                        offset: rdesc_item.offset(),
                        message,
                    })
                }
                Err(e) => return Err(e),
            },
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
            ItemType::Local(LocalItem::Reserved { value: _ }) => {}
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

        assert_eq!(0, extract_u8(&bytes, &RangeInclusive::new(0, 0)));
        assert_eq!(2, extract_u8(&bytes, &RangeInclusive::new(0, 1)));
        assert_eq!(10, extract_u8(&bytes, &RangeInclusive::new(0, 3)));

        assert_eq!(0, extract_i8(&bytes, &RangeInclusive::new(0, 0)));
        assert_eq!(-2, extract_i8(&bytes, &RangeInclusive::new(0, 1)));
        assert_eq!(-6, extract_i8(&bytes, &RangeInclusive::new(0, 3)));

        assert_eq!(0b1001_1100, extract_u8(&bytes, &RangeInclusive::new(4, 11)));
        assert_eq!(
            0b1001_1100u8 as i8,
            extract_i8(&bytes, &RangeInclusive::new(4, 11))
        );

        assert_eq!(0, extract_u16(&bytes, &RangeInclusive::new(0, 0)));
        assert_eq!(2, extract_u16(&bytes, &RangeInclusive::new(0, 1)));
        assert_eq!(10, extract_u16(&bytes, &RangeInclusive::new(0, 3)));

        assert_eq!(0, extract_i16(&bytes, &RangeInclusive::new(0, 0)));
        assert_eq!(-2, extract_i16(&bytes, &RangeInclusive::new(0, 1)));
        assert_eq!(-6, extract_i16(&bytes, &RangeInclusive::new(0, 3)));

        assert_eq!(
            0b0110_1011_1001_1100,
            extract_u16(&bytes, &RangeInclusive::new(4, 19))
        );
        assert_eq!(
            0b0110_1011_1001_1100,
            extract_i16(&bytes, &RangeInclusive::new(4, 19))
        );
        assert_eq!(
            0b1_0110_1011_1001_110u16 as i16,
            extract_i16(&bytes, &RangeInclusive::new(5, 20))
        );

        assert_eq!(
            0b0110_1011_1001_1100,
            extract_u32(&bytes, &RangeInclusive::new(4, 19))
        );
        assert_eq!(
            0b0110_1011_1001_1100,
            extract_i32(&bytes, &RangeInclusive::new(4, 19))
        );
        assert_eq!(
            ((0b1_0110_1011_1001_110u16 as i16) as i32),
            extract_i32(&bytes, &RangeInclusive::new(5, 20))
        );

        assert_eq!(
            ((0b1_0110_1011_1001_110u16 as i16) as i32),
            extract_i32(&bytes, &RangeInclusive::new(5, 20))
        );
    }
}
