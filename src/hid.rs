// SPDX-License-Identifier: MIT

//! A wrapper around the HID Core items. This module handles splitting
//! a report descriptor byte stream into its individual components.
//! Interpretation and/or analysis of the resulting [Item]s is left to
//! the caller.
//!
//! In this document and unless stated otherwise, a reference to "Section a.b.c" refers to the
//! [HID Device Class Definition for HID 1.11](https://www.usb.org/document-library/device-class-definition-hid-111).
//!
//! # Itemizing HID Report Descriptors
//!
//! Entry point is usually [`ReportDescriptorItems::try_from(bytes)`](ReportDescriptorItems::try_from):
//!
//! ```
//! # use crate::hidreport::hid::*;
//! # fn parse(bytes: &[u8]) {
//! let rdesc_items = ReportDescriptorItems::try_from(bytes).unwrap();
//! for rdesc_item in rdesc_items.iter() {
//!     println!("Item at offset {:02x}", rdesc_item.offset());
//!     let item = rdesc_item.item();
//!     match item.item_type() {
//!         ItemType::Main(mi) => match mi {
//!             MainItem::Output(o) => println!("This is an output item"),
//!             _ => {},
//!         }
//!         _ => {}
//!     }
//! }
//! # }
//! ```
//!
//! # Building HID Report Descriptors programmatically
//!
//! This module can be used to build a HID Report Descriptor from scratch.
//!
//! ```
//! # use crate::hidreport::hid::*;
//! # use crate::hidreport::types::*;
//! use hut::{self, AsUsage};
//!
//! let mut builder = ReportDescriptorBuilder::new();
//! let rdesc: Vec<u8> = builder
//!        .usage_page(hut::UsagePage::GenericDesktop)
//!        .usage_id(hut::GenericDesktop::Mouse)
//!        .open_collection(CollectionItem::Application)
//!        .open_collection(CollectionItem::Physical)
//!        .push()
//!        .append(LogicalMinimum::from(0).into())
//!        .append(LogicalMaximum::from(128).into())
//!        .pop()
//!        .append(ReportCount::from(2).into())
//!        .append(ReportSize::from(8).into())
//!        .usage_id(hut::GenericDesktop::X)
//!        .usage_id(hut::GenericDesktop::Y)
//!        .input(ItemBuilder::new()
//!               .variable()
//!               .absolute()
//!               .input())
//!        .close_collection()
//!        .close_collection()
//!        .build();
//! ```
//!
//! Note that the [ReportDescriptorBuilder] does **not** validate the items.

use crate::types::*;
use crate::{ensure, ParserError};

use thiserror::Error;

#[cfg(feature = "hut")]
use hut;

/// Convenience function to be extract a single bit as bool from a value
fn bit(bits: u32, bit: u8) -> bool {
    assert!(bit < 32);
    bits & (1 << bit) != 0
}

/// The data bytes of a HID item, guaranteed to
/// be of length 1, 2, or 4 bytes depending on the
/// input and in LE byte order.
///
/// This struct only exists for conversion from numbers to
/// a hid-compatible byte array.
struct HidBytes(Vec<u8>);

impl HidBytes {
    fn take(self) -> Vec<u8> {
        self.0
    }
}

impl std::ops::Deref for HidBytes {
    type Target = Vec<u8>;

    fn deref(&self) -> &Self::Target {
        &self.0
    }
}

impl From<u32> for HidBytes {
    fn from(value: u32) -> HidBytes {
        let bytes = value.to_le_bytes();
        let cutoff = match value {
            0..=255 => 1,
            256..=0xffff => 2,
            _ => 4,
        };
        HidBytes(bytes[0..cutoff].to_vec())
    }
}

impl From<u16> for HidBytes {
    fn from(value: u16) -> HidBytes {
        let bytes = value.to_le_bytes();
        let cutoff = match value {
            0..=255 => 1,
            _ => 2,
        };
        HidBytes(bytes[0..cutoff].to_vec())
    }
}

impl From<u8> for HidBytes {
    fn from(value: u8) -> HidBytes {
        HidBytes(vec![value])
    }
}

impl From<usize> for HidBytes {
    fn from(value: usize) -> HidBytes {
        let bytes = value.to_le_bytes();
        let cutoff = match value {
            0..=255 => 1,
            256..=0xffff => 2,
            _ => 4,
        };
        HidBytes(bytes[0..cutoff].to_vec())
    }
}

impl From<i32> for HidBytes {
    fn from(value: i32) -> HidBytes {
        const MIN16: i32 = i16::MIN as i32;
        const MAX16: i32 = i16::MAX as i32;
        let bytes = match value {
            -128..=127 => (value as i8).to_le_bytes().to_vec(),
            MIN16..=MAX16 => (value as i16).to_le_bytes().to_vec(),
            _ => value.to_le_bytes().to_vec(),
        };
        HidBytes(bytes)
    }
}

impl From<i16> for HidBytes {
    fn from(value: i16) -> HidBytes {
        let bytes = match value {
            -128..=127 => (value as i8).to_le_bytes().to_vec(),
            _ => value.to_le_bytes().to_vec(),
        };
        HidBytes(bytes)
    }
}

impl From<i8> for HidBytes {
    fn from(value: i8) -> HidBytes {
        HidBytes(vec![value as u8])
    }
}

/// Represents one value extracted from a set of (LE) bytes.
pub(crate) struct HidValue {
    value: u32,
    nbytes: usize,
}

impl HidValue {
    /// The length of the value in bytes, required to
    /// determine if the actual value may be signed
    pub(crate) fn len(&self) -> usize {
        self.nbytes
    }
}

impl TryFrom<&[u8]> for HidValue {
    type Error = HidError;

    fn try_from(bytes: &[u8]) -> Result<HidValue> {
        ensure!(!bytes.is_empty(), HidError::InsufficientData);
        let value = match bytes.len() {
            1 => bytes[0] as u32,
            2 => u16::from_le_bytes(bytes[0..2].try_into().unwrap()) as u32,
            4 => u32::from_le_bytes(bytes[0..4].try_into().unwrap()),
            _ => panic!("Size {} cannot happen", bytes.len()),
        };
        Ok(HidValue {
            value,
            nbytes: bytes.len(),
        })
    }
}

impl From<&HidValue> for usize {
    fn from(v: &HidValue) -> usize {
        v.value as usize
    }
}

impl From<HidValue> for usize {
    fn from(v: HidValue) -> usize {
        usize::from(&v)
    }
}

impl From<&HidValue> for u32 {
    fn from(v: &HidValue) -> u32 {
        v.value
    }
}

impl From<HidValue> for u32 {
    fn from(v: HidValue) -> u32 {
        u32::from(&v)
    }
}

impl From<&HidValue> for u16 {
    fn from(v: &HidValue) -> u16 {
        (v.value & 0xFFFF) as u16
    }
}

impl From<HidValue> for u16 {
    fn from(v: HidValue) -> u16 {
        u16::from(&v)
    }
}

impl From<&HidValue> for u8 {
    fn from(v: &HidValue) -> u8 {
        (v.value & 0xFF) as u8
    }
}

impl From<HidValue> for u8 {
    fn from(v: HidValue) -> u8 {
        u8::from(&v)
    }
}

impl From<&HidValue> for i32 {
    fn from(v: &HidValue) -> i32 {
        match v.len() {
            1 => ((v.value & 0xFF) as i8) as i32,
            2 => ((v.value & 0xFFFF) as i16) as i32,
            4 => v.value as i32,
            _ => panic!("Size {} cannot happen", v.len()),
        }
    }
}

impl From<HidValue> for i32 {
    fn from(v: HidValue) -> i32 {
        i32::from(&v)
    }
}

#[derive(Error, Debug)]
pub enum HidError {
    #[error("Invalid data: {message}")]
    InvalidData { message: String },
    #[error("Insufficient data")]
    InsufficientData,
}

type Result<T> = std::result::Result<T, HidError>;

/// The type of a HID item may be one of [MainItem], [GlobalItem], or [LocalItem].
/// These items comprise the report descriptor and how the report descriptor should
/// be compiled.
///
/// The special types [ItemType::Long] and [ItemType::Reserved] are primarily placeholders
/// and unlikely to be seen in the wild.
#[derive(Debug, Clone, Copy, PartialEq)]
pub enum ItemType {
    Main(MainItem),
    Global(GlobalItem),
    Local(LocalItem),
    Long,
    Reserved,
}

impl ItemType {
    /// Return the HID bytes representing this [ItemType].
    /// This is the opposite of [ItemType::try_from(u8)].
    ///
    /// ```
    /// # use crate::hidreport::hid::*;
    /// # use crate::hidreport::types::*;
    ///
    /// let item = ItemType::from(LogicalMinimum::from(128i32));
    /// let bytes = item.as_bytes();
    /// assert_eq!(bytes.len(), 3);
    /// // first byte is the LogicalMinimum prefix plus two data bytes for signed 128
    /// assert_eq!(*bytes.get(0).unwrap(), 0b00010100 + 2);
    /// assert_eq!(*bytes.get(1).unwrap(), 128);
    /// assert_eq!(*bytes.get(2).unwrap(), 0);
    ///
    /// let item2 = ItemType::try_from(bytes.as_slice()).unwrap();
    /// assert_eq!(item, item2);
    /// ```
    ///
    /// Note that [ItemType::Long] and [ItemType::Reserved] return
    /// an empty vector.
    pub fn as_bytes(&self) -> Vec<u8> {
        match self {
            ItemType::Main(item) => item.as_bytes(),
            ItemType::Global(item) => item.as_bytes(),
            ItemType::Local(item) => item.as_bytes(),
            ItemType::Long | ItemType::Reserved => vec![],
        }
    }
}

#[cfg(feature = "hut")]
impl From<&hut::UsagePage> for ItemType {
    fn from(hut: &hut::UsagePage) -> ItemType {
        GlobalItem::UsagePage(UsagePage::from(hut)).into()
    }
}

#[cfg(feature = "hut")]
impl From<hut::UsagePage> for ItemType {
    fn from(hut: hut::UsagePage) -> ItemType {
        ItemType::from(&hut)
    }
}

#[cfg(feature = "hut")]
impl From<&hut::Usage> for ItemType {
    fn from(hut: &hut::Usage) -> ItemType {
        LocalItem::Usage(UsagePage::from(hut), UsageId::from(hut)).into()
    }
}

#[cfg(feature = "hut")]
impl From<hut::Usage> for ItemType {
    fn from(hut: hut::Usage) -> ItemType {
        ItemType::from(&hut)
    }
}

impl From<MainItem> for ItemType {
    fn from(item: MainItem) -> ItemType {
        ItemType::Main(item)
    }
}

impl From<GlobalItem> for ItemType {
    fn from(item: GlobalItem) -> ItemType {
        ItemType::Global(item)
    }
}

impl From<LocalItem> for ItemType {
    fn from(item: LocalItem) -> ItemType {
        ItemType::Local(item)
    }
}

impl From<InputItem> for ItemType {
    fn from(item: InputItem) -> ItemType {
        MainItem::Input(item).into()
    }
}

impl From<OutputItem> for ItemType {
    fn from(item: OutputItem) -> ItemType {
        MainItem::Output(item).into()
    }
}

impl From<FeatureItem> for ItemType {
    fn from(item: FeatureItem) -> ItemType {
        MainItem::Feature(item).into()
    }
}

impl From<CollectionItem> for ItemType {
    fn from(item: CollectionItem) -> ItemType {
        MainItem::Collection(item).into()
    }
}

impl From<UsagePage> for ItemType {
    fn from(usage_page: UsagePage) -> ItemType {
        GlobalItem::UsagePage(usage_page).into()
    }
}

impl From<LogicalMinimum> for ItemType {
    fn from(minimum: LogicalMinimum) -> ItemType {
        GlobalItem::LogicalMinimum(minimum).into()
    }
}

impl From<LogicalMaximum> for ItemType {
    fn from(maximum: LogicalMaximum) -> ItemType {
        GlobalItem::LogicalMaximum(maximum).into()
    }
}

impl From<PhysicalMinimum> for ItemType {
    fn from(minimum: PhysicalMinimum) -> ItemType {
        GlobalItem::PhysicalMinimum(minimum).into()
    }
}

impl From<PhysicalMaximum> for ItemType {
    fn from(maximum: PhysicalMaximum) -> ItemType {
        GlobalItem::PhysicalMaximum(maximum).into()
    }
}

impl From<UnitExponent> for ItemType {
    fn from(exponent: UnitExponent) -> ItemType {
        GlobalItem::UnitExponent(exponent).into()
    }
}

impl From<ReportSize> for ItemType {
    fn from(size: ReportSize) -> ItemType {
        GlobalItem::ReportSize(size).into()
    }
}

impl From<ReportId> for ItemType {
    fn from(id: ReportId) -> ItemType {
        GlobalItem::ReportId(id).into()
    }
}

impl From<ReportCount> for ItemType {
    fn from(count: ReportCount) -> ItemType {
        GlobalItem::ReportCount(count).into()
    }
}

impl From<UsageId> for ItemType {
    fn from(usage_id: UsageId) -> ItemType {
        LocalItem::UsageId(usage_id).into()
    }
}

impl From<(UsagePage, UsageId)> for ItemType {
    fn from(usage: (UsagePage, UsageId)) -> ItemType {
        LocalItem::Usage(usage.0, usage.1).into()
    }
}

impl From<UsageMinimum> for ItemType {
    fn from(minimum: UsageMinimum) -> ItemType {
        LocalItem::UsageMinimum(minimum).into()
    }
}

impl From<UsageMaximum> for ItemType {
    fn from(maximum: UsageMaximum) -> ItemType {
        LocalItem::UsageMaximum(maximum).into()
    }
}

impl From<DesignatorMinimum> for ItemType {
    fn from(minimum: DesignatorMinimum) -> ItemType {
        LocalItem::DesignatorMinimum(minimum).into()
    }
}

impl From<DesignatorMaximum> for ItemType {
    fn from(maximum: DesignatorMaximum) -> ItemType {
        LocalItem::DesignatorMaximum(maximum).into()
    }
}

impl From<DesignatorIndex> for ItemType {
    fn from(index: DesignatorIndex) -> ItemType {
        LocalItem::DesignatorIndex(index).into()
    }
}

impl From<StringMinimum> for ItemType {
    fn from(minimum: StringMinimum) -> ItemType {
        LocalItem::StringMinimum(minimum).into()
    }
}

impl From<StringMaximum> for ItemType {
    fn from(maximum: StringMaximum) -> ItemType {
        LocalItem::StringMaximum(maximum).into()
    }
}

impl From<StringIndex> for ItemType {
    fn from(index: StringIndex) -> ItemType {
        LocalItem::StringIndex(index).into()
    }
}

impl From<Delimiter> for ItemType {
    fn from(delimiter: Delimiter) -> ItemType {
        LocalItem::Delimiter(delimiter).into()
    }
}

/// Main Items, see Section 6.2.2.4
///
/// > Main items are used to either define or group certain types of data fields within a
/// > Report descriptor. There are two types of Main items: data and non-data. Data-
/// > type Main items are used to create a field within a report and include Input,
/// > Output, and Feature. Other items do not create fields and are subsequently
/// > referred to as non-data Main items.
#[derive(Debug, Clone, Copy, PartialEq)]
pub enum MainItem {
    Input(InputItem),
    Output(OutputItem),
    Feature(FeatureItem),
    Collection(CollectionItem),
    EndCollection,
}

impl MainItem {
    pub fn as_bytes(&self) -> Vec<u8> {
        match self {
            MainItem::Input(item) => item.as_bytes(),
            MainItem::Output(item) => item.as_bytes(),
            MainItem::Feature(item) => item.as_bytes(),
            MainItem::Collection(item) => item.as_bytes(),
            MainItem::EndCollection => vec![0b11000000],
        }
    }
}

/// Main Data Item, see Section 6.2.5.
///
/// A data item is a [MainItem] that "create a field within a report and include Input,
/// Output, and Feature.". These have shared properties provided by this trait.
///
/// These properties come in pairs (bit set or unset in the HID report descriptor item),
/// for readability in the caller, a function is provided for each state.
pub trait MainDataItem {
    /// True if the data is constant and never changes. This typically means the data
    /// can be ignored.
    ///
    /// Mutually exclusive with [MainDataItem::is_data].
    fn is_constant(&self) -> bool;

    /// True if the field carries data.
    ///
    /// Mutually exclusive with [MainDataItem::is_constant].
    fn is_data(&self) -> bool {
        !self.is_constant()
    }

    /// True if the data is a variable field.
    ///
    /// Mutually exclusive with [MainDataItem::is_array].
    fn is_variable(&self) -> bool;

    /// True if the data is an array field.
    ///
    /// Mutually exclusive with [MainDataItem::is_variable].
    fn is_array(&self) -> bool {
        !self.is_variable()
    }

    /// True if the data is relative compared to a previous report
    ///
    /// Mutually exclusive with [MainDataItem::is_absolute].
    fn is_relative(&self) -> bool;

    /// True if the data is absolute
    ///
    /// Mutually exclusive with [MainDataItem::is_relative].
    fn is_absolute(&self) -> bool {
        !self.is_relative()
    }

    /// True if the data wraps around at the logical
    /// minimum/maximum (e.g. a dial that can spin at 360 degrees).
    ///
    /// Mutually exclusive with [MainDataItem::does_not_wrap].
    fn wraps(&self) -> bool;

    /// True if the data does not wrap at the logical
    /// minimum/maximum.
    ///
    /// Mutually exclusive with [MainDataItem::wraps].
    fn does_not_wrap(&self) -> bool {
        !self.wraps()
    }

    /// True if the data was pre-processed on the device
    /// and the logical range is not linear.
    ///
    /// Mutually exclusive with [MainDataItem::is_linear].
    fn is_nonlinear(&self) -> bool;

    /// True if the data was not pre-processed on the device
    /// and the logical range is linear.
    ///
    /// Mutually exclusive with [MainDataItem::is_nonlinear].
    fn is_linear(&self) -> bool {
        !self.is_nonlinear()
    }

    /// True if the control does not have a preferred state it
    /// returns to when the user stops interacting (e.g. a joystick
    /// may return to a neutral position)
    ///
    /// Mutually exclusive with [MainDataItem::has_preferred_state].
    fn has_no_preferred_state(&self) -> bool;

    /// True if the control does not ave a preferred state.
    ///
    /// Mutually exclusive with [MainDataItem::has_no_preferred_state].
    fn has_preferred_state(&self) -> bool {
        !self.has_no_preferred_state()
    }

    /// True if the control has a null state where it does not send
    /// data (e.g. a joystick in neutral state)
    ///
    /// Mutually exclusive with [MainDataItem::has_no_null_state].
    fn has_null_state(&self) -> bool;

    /// True if the control does not have a null state where it does not send
    /// data.
    ///
    /// Mutually exclusive with [MainDataItem::has_null_state].
    fn has_no_null_state(&self) -> bool {
        !self.has_null_state()
    }

    /// True if the control emits a fixed size stream of bytes.
    ///
    /// Mutually exclusive with [MainDataItem::is_bitfield].
    fn is_buffered_bytes(&self) -> bool;

    /// True if the control is a single bit field (value).
    ///
    /// Mutually exclusive with [MainDataItem::is_buffered_bytes].
    fn is_bitfield(&self) -> bool {
        !self.is_buffered_bytes()
    }
}

/// From Section 6.2.2.4.
/// > [Input](InputItem), [Output](OutputItem), and [Feature](FeatureItem)
/// > items are used to create data fields within a report.
/// >
/// > An Input item describes information about the data provided by one or more
/// > physical controls. An application can use this information to interpret the data
/// > provided by the device. All data fields defined in a single item share an
/// > identical data format.
/// >
/// > The Output item is used to define an output data field in a report. This item is
/// > similar to an Input item except it describes data sent to the device—for
/// > example, LED states.
/// >
/// > Feature items describe device configuration information that can be sent to
/// > the device.
#[derive(Debug, Clone, Copy, Default, PartialEq)]
pub struct InputItem {
    /// This item is constant if `true` (and thus can usually be ignored).
    /// If false, the item refers to a data field.
    is_constant: bool,
    /// Array or single variable
    is_variable: bool,
    /// Absolute or relative
    is_relative: bool,
    /// Data wraps around after exceeding minimum or maximum
    wraps: bool,
    /// Raw data from the devise has been processed on the device and is no longer linear
    is_nonlinear: bool,
    /// Control has a preferred state or not
    has_no_preferred_state: bool,
    /// Control has a neutral state where it does not send meaningful data
    has_null_state: bool,
    /// Indicates whether the field emits a fixed size stream of bytes
    is_buffered_bytes: bool,
}

impl InputItem {
    pub fn as_bytes(&self) -> Vec<u8> {
        let len = if self.is_buffered_bytes { 2 } else { 1 };
        let prefix = 0b10000000 + len;
        let mut flags: u16 = 0;

        if self.is_constant {
            flags |= 1 << 0;
        }
        if self.is_variable {
            flags |= 1 << 1;
        }
        if self.is_relative {
            flags |= 1 << 2;
        }
        if self.wraps {
            flags |= 1 << 3;
        }
        if self.is_nonlinear {
            flags |= 1 << 4;
        }
        if self.has_no_preferred_state {
            flags |= 1 << 5;
        }
        if self.has_null_state {
            flags |= 1 << 6;
        }
        if self.is_buffered_bytes {
            flags |= 1 << 8;
            vec![prefix, (flags & 0xff) as u8, ((flags >> 8) & 0xff) as u8]
        } else {
            vec![prefix, (flags & 0xff) as u8]
        }
    }
}

/// See Section 6.2.2.5. Equivalent to the [InputItem], please
/// refer to that documentation.
///
/// The only difference to the [InputItem] is the existence of the
/// the [OutputItem::is_volatile].
#[derive(Debug, Clone, Copy, Default, PartialEq)]
pub struct OutputItem {
    /// This item is constant if `true` (and thus can usually be ignored).
    /// If false, the item refers to a data field.
    is_constant: bool,
    /// Array or single variable
    is_variable: bool,
    /// Absolute or relative
    is_relative: bool,
    /// Data wraps around after exceeding minimum or maximum
    wraps: bool,
    /// Raw data from the devise has been processed on the device and is no longer linear
    is_nonlinear: bool,
    /// Control has a preferred state or not
    has_no_preferred_state: bool,
    /// Control has a neutral state where it does not send meaningful data
    has_null_state: bool,
    /// Indiciates whether control should be changed by the host.
    is_volatile: bool,
    /// Indicates whether the field emits a fixed size stream of bytes
    is_buffered_bytes: bool,
}

impl OutputItem {
    pub fn is_volatile(&self) -> bool {
        self.is_volatile
    }

    pub fn is_nonvolatile(&self) -> bool {
        !self.is_volatile()
    }

    pub fn as_bytes(&self) -> Vec<u8> {
        let len = if self.is_buffered_bytes { 2 } else { 1 };
        let prefix = 0b10010000 + len;
        let mut flags: u16 = 0;

        if self.is_constant {
            flags |= 1 << 0;
        }
        if self.is_variable {
            flags |= 1 << 1;
        }
        if self.is_relative {
            flags |= 1 << 2;
        }
        if self.wraps {
            flags |= 1 << 3;
        }
        if self.is_nonlinear {
            flags |= 1 << 4;
        }
        if self.has_no_preferred_state {
            flags |= 1 << 5;
        }
        if self.has_null_state {
            flags |= 1 << 6;
        }
        if self.is_volatile {
            flags |= 1 << 7;
        }
        if self.is_buffered_bytes {
            flags |= 1 << 8;
            vec![prefix, (flags & 0xff) as u8, ((flags >> 8) & 0xff) as u8]
        } else {
            vec![prefix, (flags & 0xff) as u8]
        }
    }
}

impl MainDataItem for OutputItem {
    fn is_constant(&self) -> bool {
        self.is_constant
    }

    fn is_variable(&self) -> bool {
        self.is_variable
    }

    fn is_relative(&self) -> bool {
        self.is_relative
    }

    fn wraps(&self) -> bool {
        self.wraps
    }

    fn is_nonlinear(&self) -> bool {
        self.is_nonlinear
    }

    fn has_no_preferred_state(&self) -> bool {
        self.has_no_preferred_state
    }

    fn has_null_state(&self) -> bool {
        self.has_null_state
    }

    fn is_buffered_bytes(&self) -> bool {
        self.is_buffered_bytes
    }
}

/// See Section 6.2.2.5. Equivalent to the [InputItem], please
/// refer to that documentation.
///
/// The only difference to the [InputItem] is the existence of the
/// the [FeatureItem::is_volatile].
#[derive(Debug, Clone, Copy, Default, PartialEq)]
pub struct FeatureItem {
    /// This item is constant if `true` (and thus can usually be ignored).
    /// If false, the item refers to a data field.
    is_constant: bool,
    /// Array or single variable
    is_variable: bool,
    /// Absolute or relative
    is_relative: bool,
    /// Data wraps around after exceeding minimum or maximum
    wraps: bool,
    /// Raw data from the devise has been processed on the device and is no longer linear
    is_nonlinear: bool,
    /// Control has a preferred state or not
    has_no_preferred_state: bool,
    /// Control has a neutral state where it does not send meaningful data
    has_null_state: bool,
    /// Indiciates whether control should be changed by the host.
    is_volatile: bool,
    /// Indicates whether the field emits a fixed size stream of bytes
    is_buffered_bytes: bool,
}

impl FeatureItem {
    /// True if the control value should be changed by the host
    pub fn is_volatile(&self) -> bool {
        self.is_volatile
    }

    /// False if the control value should not be changed by the host
    pub fn is_nonvolatile(&self) -> bool {
        !self.is_volatile()
    }

    pub fn as_bytes(&self) -> Vec<u8> {
        let len = if self.is_buffered_bytes { 2 } else { 1 };
        let prefix = 0b10110000 + len;
        let mut flags: u16 = 0;

        if self.is_constant {
            flags |= 1 << 0;
        }
        if self.is_variable {
            flags |= 1 << 1;
        }
        if self.is_relative {
            flags |= 1 << 2;
        }
        if self.wraps {
            flags |= 1 << 3;
        }
        if self.is_nonlinear {
            flags |= 1 << 4;
        }
        if self.has_no_preferred_state {
            flags |= 1 << 5;
        }
        if self.has_null_state {
            flags |= 1 << 6;
        }
        if self.is_volatile {
            flags |= 1 << 7;
        }
        if self.is_buffered_bytes {
            flags |= 1 << 8;
            vec![prefix, (flags & 0xff) as u8, ((flags >> 8) & 0xff) as u8]
        } else {
            vec![prefix, (flags & 0xff) as u8]
        }
    }
}

impl MainDataItem for FeatureItem {
    fn is_constant(&self) -> bool {
        self.is_constant
    }

    fn is_variable(&self) -> bool {
        self.is_variable
    }

    fn is_relative(&self) -> bool {
        self.is_relative
    }

    fn wraps(&self) -> bool {
        self.wraps
    }

    fn is_nonlinear(&self) -> bool {
        self.is_nonlinear
    }

    fn has_no_preferred_state(&self) -> bool {
        self.has_no_preferred_state
    }

    fn has_null_state(&self) -> bool {
        self.has_null_state
    }

    fn is_buffered_bytes(&self) -> bool {
        self.is_buffered_bytes
    }
}

// Implementation for the ItemBuilder and it's type states -
// each of the possible flags has Undefined, A, B and in
// the implementation of the ItemBuilder each state can be
// set only once.
macro_rules! impl_ibstate {
    ($t:ident, $a:ident, $b:ident) => {
        #[doc(hidden)]
        pub trait $t {}
        #[doc(hidden)]
        pub enum $a {}
        #[doc(hidden)]
        pub enum $b {}
        impl $t for $a {}
        impl $t for $b {}
        impl $t for IBUndefined {}
    };
}

#[doc(hidden)]
pub enum IBUndefined {}

// Naming: IBS == Item Builder State
impl_ibstate!(IBSData, IBData, IBConstant);
impl_ibstate!(IBSArr, IBVariable, IBArray);
impl_ibstate!(IBSAbs, IBAbsolute, IBRelative);
impl_ibstate!(IBSWrap, IBWrap, IBNoWrap);
impl_ibstate!(IBSLin, IBLinear, IBNonLinear);
impl_ibstate!(IBSPref, IBPreferred, IBNoPreferred);
impl_ibstate!(IBSNull, IBNull, IBNoNull);
impl_ibstate!(IBSVol, IBVolatile, IBNonVolatile);
impl_ibstate!(IBSBit, IBBitfield, IBBuffered);

/// Builder for an [InputItem], [OutputItem], or [FeatureItem].
///
/// Only flags that differ from the default need to be set, the most common
/// invocations of this builder are a variation of:
///
/// ```
/// # use crate::hidreport::hid::*;
/// let item: InputItem = ItemBuilder::new()
///            .variable()
///            .absolute()
///            .input();
/// let item: OutputItem = ItemBuilder::new()
///            .constant()
///            .output();
/// let item: FeatureItem = ItemBuilder::new()
///            .array()
///            .relative()
///            .feature();
/// ```
///
#[derive(Default)]
pub struct ItemBuilder<A, B, C, D, E, F, G, H, I>
where
    A: IBSData,
    B: IBSArr,
    C: IBSAbs,
    D: IBSWrap,
    E: IBSLin,
    F: IBSPref,
    G: IBSNull,
    H: IBSBit,
    I: IBSVol,
{
    // Use an OutputItem here because it has volatile
    item: OutputItem,
    m1: std::marker::PhantomData<A>,
    m2: std::marker::PhantomData<B>,
    m3: std::marker::PhantomData<C>,
    m4: std::marker::PhantomData<D>,
    m5: std::marker::PhantomData<E>,
    m6: std::marker::PhantomData<F>,
    m7: std::marker::PhantomData<G>,
    m8: std::marker::PhantomData<H>,
    m9: std::marker::PhantomData<I>,
}

impl
    ItemBuilder<
        IBUndefined,
        IBUndefined,
        IBUndefined,
        IBUndefined,
        IBUndefined,
        IBUndefined,
        IBUndefined,
        IBUndefined,
        IBUndefined,
    >
{
    /// Create a new builder for an [InputItem], [OutputItem] or [FeatureItem]. Each flag on the
    /// builder may only be set once, complete the item by calling
    /// [ItemBuilder::input()], [ItemBuilder::output()] or [ItemBuilder::feature()].
    ///
    /// ```
    /// # use crate::hidreport::hid::*;
    /// let item: InputItem = ItemBuilder::new()
    ///            .data()
    ///            .variable()
    ///            .absolute()
    ///            .input();
    /// ```
    /// Where an item flag is not set the default (unset) is used. See
    /// Section 6.2.2.5 "Input, Output, and Feature Items" for details
    /// on default flags.
    pub fn new() -> ItemBuilder<
        IBUndefined,
        IBUndefined,
        IBUndefined,
        IBUndefined,
        IBUndefined,
        IBUndefined,
        IBUndefined,
        IBUndefined,
        IBUndefined,
    > {
        ItemBuilder {
            item: OutputItem::default(),
            m1: std::marker::PhantomData,
            m2: std::marker::PhantomData,
            m3: std::marker::PhantomData,
            m4: std::marker::PhantomData,
            m5: std::marker::PhantomData,
            m6: std::marker::PhantomData,
            m7: std::marker::PhantomData,
            m8: std::marker::PhantomData,
            m9: std::marker::PhantomData,
        }
    }
}

impl<A, B, C, D, E, F, G, H, I> ItemBuilder<A, B, C, D, E, F, G, H, I>
where
    A: IBSData,
    B: IBSArr,
    C: IBSAbs,
    D: IBSWrap,
    E: IBSLin,
    F: IBSPref,
    G: IBSNull,
    H: IBSBit,
    I: IBSVol,
{
    /// Convert the current builder to an [InputItem].
    /// ```
    /// # use crate::hidreport::hid::*;
    /// let item: InputItem = ItemBuilder::new()
    ///            .data()
    ///            .variable()
    ///            .absolute()
    ///            .input();
    /// assert!(item.is_data() && !item.is_constant());
    /// assert!(item.is_variable() && !item.is_array());
    /// assert!(item.is_absolute() && !item.is_relative());
    /// ```
    pub fn input(self) -> InputItem {
        InputItem {
            is_constant: self.item.is_constant,
            is_variable: self.item.is_variable,
            is_relative: self.item.is_relative,
            wraps: self.item.wraps,
            is_nonlinear: self.item.is_nonlinear,
            has_no_preferred_state: self.item.has_no_preferred_state,
            has_null_state: self.item.has_null_state,
            is_buffered_bytes: self.item.is_buffered_bytes,
        }
    }

    /// Convert the current builder to an [OutputItem].
    /// ```
    /// # use crate::hidreport::hid::*;
    /// let item: OutputItem = ItemBuilder::new()
    ///            .data()
    ///            .variable()
    ///            .absolute()
    ///            .output();
    /// assert!(item.is_data() && !item.is_constant());
    /// assert!(item.is_variable() && !item.is_array());
    /// assert!(item.is_absolute() && !item.is_relative());
    /// ```
    pub fn output(self) -> OutputItem {
        self.item
    }

    /// Convert the current builder to a [FeatureItem].
    /// ```
    /// # use crate::hidreport::hid::*;
    /// let item: FeatureItem = ItemBuilder::new()
    ///            .data()
    ///            .variable()
    ///            .absolute()
    ///            .feature();
    /// assert!(item.is_data() && !item.is_constant());
    /// assert!(item.is_variable() && !item.is_array());
    /// assert!(item.is_absolute() && !item.is_relative());
    /// ```
    pub fn feature(self) -> FeatureItem {
        FeatureItem {
            is_constant: self.item.is_constant,
            is_variable: self.item.is_variable,
            is_relative: self.item.is_relative,
            wraps: self.item.wraps,
            is_nonlinear: self.item.is_nonlinear,
            has_no_preferred_state: self.item.has_no_preferred_state,
            has_null_state: self.item.has_null_state,
            is_volatile: self.item.is_volatile,
            is_buffered_bytes: self.item.is_buffered_bytes,
        }
    }
}

impl<B, C, D, E, F, G, H, I> ItemBuilder<IBUndefined, B, C, D, E, F, G, H, I>
where
    B: IBSArr,
    C: IBSAbs,
    D: IBSWrap,
    E: IBSLin,
    F: IBSPref,
    G: IBSNull,
    H: IBSBit,
    I: IBSVol,
{
    /// Set the item data to be constant.
    pub fn constant(mut self) -> ItemBuilder<IBConstant, B, C, D, E, F, G, H, I> {
        self.item.is_constant = true;
        ItemBuilder {
            item: self.item,
            m1: std::marker::PhantomData,
            m2: std::marker::PhantomData,
            m3: std::marker::PhantomData,
            m4: std::marker::PhantomData,
            m5: std::marker::PhantomData,
            m6: std::marker::PhantomData,
            m7: std::marker::PhantomData,
            m8: std::marker::PhantomData,
            m9: std::marker::PhantomData,
        }
    }

    /// Set the item data to be data. This is the default.
    pub fn data(mut self) -> ItemBuilder<IBData, B, C, D, E, F, G, H, I> {
        self.item.is_constant = false;
        ItemBuilder {
            item: self.item,
            m1: std::marker::PhantomData,
            m2: std::marker::PhantomData,
            m3: std::marker::PhantomData,
            m4: std::marker::PhantomData,
            m5: std::marker::PhantomData,
            m6: std::marker::PhantomData,
            m7: std::marker::PhantomData,
            m8: std::marker::PhantomData,
            m9: std::marker::PhantomData,
        }
    }
}

impl<A, C, D, E, F, G, H, I> ItemBuilder<A, IBUndefined, C, D, E, F, G, H, I>
where
    A: IBSData,
    C: IBSAbs,
    D: IBSWrap,
    E: IBSLin,
    F: IBSPref,
    G: IBSNull,
    H: IBSBit,
    I: IBSVol,
{
    /// Set the item data to be a variable
    pub fn variable(mut self) -> ItemBuilder<A, IBVariable, C, D, E, F, G, H, I> {
        self.item.is_variable = true;
        ItemBuilder {
            item: self.item,
            m1: std::marker::PhantomData,
            m2: std::marker::PhantomData,
            m3: std::marker::PhantomData,
            m4: std::marker::PhantomData,
            m5: std::marker::PhantomData,
            m6: std::marker::PhantomData,
            m7: std::marker::PhantomData,
            m8: std::marker::PhantomData,
            m9: std::marker::PhantomData,
        }
    }

    /// Set the item data to be an array. This is the default.
    pub fn array(mut self) -> ItemBuilder<A, IBArray, C, D, E, F, G, H, I> {
        self.item.is_variable = false;
        ItemBuilder {
            item: self.item,
            m1: std::marker::PhantomData,
            m2: std::marker::PhantomData,
            m3: std::marker::PhantomData,
            m4: std::marker::PhantomData,
            m5: std::marker::PhantomData,
            m6: std::marker::PhantomData,
            m7: std::marker::PhantomData,
            m8: std::marker::PhantomData,
            m9: std::marker::PhantomData,
        }
    }
}

impl<A, B, D, E, F, G, H, I> ItemBuilder<A, B, IBUndefined, D, E, F, G, H, I>
where
    A: IBSData,
    B: IBSArr,
    D: IBSWrap,
    E: IBSLin,
    F: IBSPref,
    G: IBSNull,
    H: IBSBit,
    I: IBSVol,
{
    /// Set the item data to represent absolute values. This is the default.
    pub fn absolute(mut self) -> ItemBuilder<A, B, IBAbsolute, D, E, F, G, H, I> {
        self.item.is_relative = false;
        ItemBuilder {
            item: self.item,
            m1: std::marker::PhantomData,
            m2: std::marker::PhantomData,
            m3: std::marker::PhantomData,
            m4: std::marker::PhantomData,
            m5: std::marker::PhantomData,
            m6: std::marker::PhantomData,
            m7: std::marker::PhantomData,
            m8: std::marker::PhantomData,
            m9: std::marker::PhantomData,
        }
    }

    /// Set the item data to represent relative values.
    pub fn relative(mut self) -> ItemBuilder<A, B, IBRelative, D, E, F, G, H, I> {
        self.item.is_relative = true;
        ItemBuilder {
            item: self.item,
            m1: std::marker::PhantomData,
            m2: std::marker::PhantomData,
            m3: std::marker::PhantomData,
            m4: std::marker::PhantomData,
            m5: std::marker::PhantomData,
            m6: std::marker::PhantomData,
            m7: std::marker::PhantomData,
            m8: std::marker::PhantomData,
            m9: std::marker::PhantomData,
        }
    }
}

impl<A, B, C, E, F, G, H, I> ItemBuilder<A, B, C, IBUndefined, E, F, G, H, I>
where
    A: IBSData,
    B: IBSArr,
    C: IBSAbs,
    E: IBSLin,
    F: IBSPref,
    G: IBSNull,
    H: IBSBit,
    I: IBSVol,
{
    /// Set the item data to wrap at the logical extents.
    pub fn wrap(mut self) -> ItemBuilder<A, B, C, IBWrap, E, F, G, H, I> {
        self.item.wraps = true;
        ItemBuilder {
            item: self.item,
            m1: std::marker::PhantomData,
            m2: std::marker::PhantomData,
            m3: std::marker::PhantomData,
            m4: std::marker::PhantomData,
            m5: std::marker::PhantomData,
            m6: std::marker::PhantomData,
            m7: std::marker::PhantomData,
            m8: std::marker::PhantomData,
            m9: std::marker::PhantomData,
        }
    }

    /// Set the item data to not wrap at the logical extents. This is the default.
    pub fn nowrap(mut self) -> ItemBuilder<A, B, C, IBNoWrap, E, F, G, H, I> {
        self.item.wraps = false;
        ItemBuilder {
            item: self.item,
            m1: std::marker::PhantomData,
            m2: std::marker::PhantomData,
            m3: std::marker::PhantomData,
            m4: std::marker::PhantomData,
            m5: std::marker::PhantomData,
            m6: std::marker::PhantomData,
            m7: std::marker::PhantomData,
            m8: std::marker::PhantomData,
            m9: std::marker::PhantomData,
        }
    }
}

impl<A, B, C, D, F, G, H, I> ItemBuilder<A, B, C, D, IBUndefined, F, G, H, I>
where
    A: IBSData,
    B: IBSArr,
    C: IBSAbs,
    D: IBSWrap,
    F: IBSPref,
    G: IBSNull,
    H: IBSBit,
    I: IBSVol,
{
    /// Set the item data to be linear.
    pub fn linear(mut self) -> ItemBuilder<A, B, C, D, IBLinear, F, G, H, I> {
        self.item.is_nonlinear = false;
        ItemBuilder {
            item: self.item,
            m1: std::marker::PhantomData,
            m2: std::marker::PhantomData,
            m3: std::marker::PhantomData,
            m4: std::marker::PhantomData,
            m5: std::marker::PhantomData,
            m6: std::marker::PhantomData,
            m7: std::marker::PhantomData,
            m8: std::marker::PhantomData,
            m9: std::marker::PhantomData,
        }
    }

    /// Set the item data to be non linear. This is the default.
    pub fn nonlinear(mut self) -> ItemBuilder<A, B, C, D, IBNonLinear, F, G, H, I> {
        self.item.is_nonlinear = true;
        ItemBuilder {
            item: self.item,
            m1: std::marker::PhantomData,
            m2: std::marker::PhantomData,
            m3: std::marker::PhantomData,
            m4: std::marker::PhantomData,
            m5: std::marker::PhantomData,
            m6: std::marker::PhantomData,
            m7: std::marker::PhantomData,
            m8: std::marker::PhantomData,
            m9: std::marker::PhantomData,
        }
    }
}

impl<A, B, C, D, E, G, H, I> ItemBuilder<A, B, C, D, E, IBUndefined, G, H, I>
where
    A: IBSData,
    B: IBSArr,
    C: IBSAbs,
    D: IBSWrap,
    E: IBSLin,
    G: IBSNull,
    H: IBSBit,
    I: IBSVol,
{
    /// Set the item data to have a preferred state.
    pub fn preferred_state(mut self) -> ItemBuilder<A, B, C, D, E, IBPreferred, G, H, I> {
        self.item.has_no_preferred_state = false;
        ItemBuilder {
            item: self.item,
            m1: std::marker::PhantomData,
            m2: std::marker::PhantomData,
            m3: std::marker::PhantomData,
            m4: std::marker::PhantomData,
            m5: std::marker::PhantomData,
            m6: std::marker::PhantomData,
            m7: std::marker::PhantomData,
            m8: std::marker::PhantomData,
            m9: std::marker::PhantomData,
        }
    }

    /// Set the item data to not have a preferred state. This is the default.
    pub fn no_preferred_state(mut self) -> ItemBuilder<A, B, C, D, E, IBNoPreferred, G, H, I> {
        self.item.has_no_preferred_state = true;
        ItemBuilder {
            item: self.item,
            m1: std::marker::PhantomData,
            m2: std::marker::PhantomData,
            m3: std::marker::PhantomData,
            m4: std::marker::PhantomData,
            m5: std::marker::PhantomData,
            m6: std::marker::PhantomData,
            m7: std::marker::PhantomData,
            m8: std::marker::PhantomData,
            m9: std::marker::PhantomData,
        }
    }
}

impl<A, B, C, D, E, F, H, I> ItemBuilder<A, B, C, D, E, F, IBUndefined, H, I>
where
    A: IBSData,
    B: IBSArr,
    C: IBSAbs,
    D: IBSWrap,
    E: IBSLin,
    F: IBSPref,
    H: IBSBit,
    I: IBSVol,
{
    /// Set the item data to have a null state
    pub fn null(mut self) -> ItemBuilder<A, B, C, D, E, F, IBNull, H, I> {
        self.item.has_null_state = true;
        ItemBuilder {
            item: self.item,
            m1: std::marker::PhantomData,
            m2: std::marker::PhantomData,
            m3: std::marker::PhantomData,
            m4: std::marker::PhantomData,
            m5: std::marker::PhantomData,
            m6: std::marker::PhantomData,
            m7: std::marker::PhantomData,
            m8: std::marker::PhantomData,
            m9: std::marker::PhantomData,
        }
    }

    /// Set the item data to not have a null state. This is the default.
    pub fn no_null(mut self) -> ItemBuilder<A, B, C, D, E, F, IBNoNull, H, I> {
        self.item.has_null_state = false;
        ItemBuilder {
            item: self.item,
            m1: std::marker::PhantomData,
            m2: std::marker::PhantomData,
            m3: std::marker::PhantomData,
            m4: std::marker::PhantomData,
            m5: std::marker::PhantomData,
            m6: std::marker::PhantomData,
            m7: std::marker::PhantomData,
            m8: std::marker::PhantomData,
            m9: std::marker::PhantomData,
        }
    }
}

impl<A, B, C, D, E, F, G, I> ItemBuilder<A, B, C, D, E, F, G, IBUndefined, I>
where
    A: IBSData,
    B: IBSArr,
    C: IBSAbs,
    D: IBSWrap,
    E: IBSLin,
    F: IBSPref,
    G: IBSNull,
    I: IBSVol,
{
    /// Set the item data to be a bit field. This is the default.
    pub fn bitfield(mut self) -> ItemBuilder<A, B, C, D, E, F, G, IBBitfield, I> {
        self.item.is_buffered_bytes = false;
        ItemBuilder {
            item: self.item,
            m1: std::marker::PhantomData,
            m2: std::marker::PhantomData,
            m3: std::marker::PhantomData,
            m4: std::marker::PhantomData,
            m5: std::marker::PhantomData,
            m6: std::marker::PhantomData,
            m7: std::marker::PhantomData,
            m8: std::marker::PhantomData,
            m9: std::marker::PhantomData,
        }
    }

    /// Set the item data to be stream of buffered bytes.
    pub fn buffered_bytes(mut self) -> ItemBuilder<A, B, C, D, E, F, G, IBBuffered, I> {
        self.item.is_buffered_bytes = true;
        ItemBuilder {
            item: self.item,
            m1: std::marker::PhantomData,
            m2: std::marker::PhantomData,
            m3: std::marker::PhantomData,
            m4: std::marker::PhantomData,
            m5: std::marker::PhantomData,
            m6: std::marker::PhantomData,
            m7: std::marker::PhantomData,
            m8: std::marker::PhantomData,
            m9: std::marker::PhantomData,
        }
    }
}

impl<A, B, C, D, E, F, G, H> ItemBuilder<A, B, C, D, E, F, G, H, IBUndefined>
where
    A: IBSData,
    B: IBSArr,
    C: IBSAbs,
    D: IBSWrap,
    E: IBSLin,
    F: IBSPref,
    G: IBSNull,
    H: IBSBit,
{
    /// Set the item data to be volatile.
    ///
    /// If the builder is later converted to an [InputItem] this flag is ignored.
    pub fn volatile(mut self) -> ItemBuilder<A, B, C, D, E, F, G, H, IBVolatile> {
        self.item.is_volatile = true;
        ItemBuilder {
            item: self.item,
            m1: std::marker::PhantomData,
            m2: std::marker::PhantomData,
            m3: std::marker::PhantomData,
            m4: std::marker::PhantomData,
            m5: std::marker::PhantomData,
            m6: std::marker::PhantomData,
            m7: std::marker::PhantomData,
            m8: std::marker::PhantomData,
            m9: std::marker::PhantomData,
        }
    }

    /// Set the item data to be stream of buffered bytes.
    ///
    /// If the builder is later converted to an [InputItem] this flag is ignored.
    pub fn non_volatile(mut self) -> ItemBuilder<A, B, C, D, E, F, G, H, IBNonVolatile> {
        self.item.is_volatile = false;
        ItemBuilder {
            item: self.item,
            m1: std::marker::PhantomData,
            m2: std::marker::PhantomData,
            m3: std::marker::PhantomData,
            m4: std::marker::PhantomData,
            m5: std::marker::PhantomData,
            m6: std::marker::PhantomData,
            m7: std::marker::PhantomData,
            m8: std::marker::PhantomData,
            m9: std::marker::PhantomData,
        }
    }
}

impl MainDataItem for InputItem {
    fn is_constant(&self) -> bool {
        self.is_constant
    }

    fn is_variable(&self) -> bool {
        self.is_variable
    }

    fn is_relative(&self) -> bool {
        self.is_relative
    }

    fn wraps(&self) -> bool {
        self.wraps
    }

    fn is_nonlinear(&self) -> bool {
        self.is_nonlinear
    }

    fn has_no_preferred_state(&self) -> bool {
        self.has_no_preferred_state
    }

    fn has_null_state(&self) -> bool {
        self.has_null_state
    }

    fn is_buffered_bytes(&self) -> bool {
        self.is_buffered_bytes
    }
}

/// See Section 6.2.2.6. A collection groups several items together.
///
/// > A Collection item identifies a relationship between two or more data (Input,
/// > Output, or Feature.) For example, a mouse could be described as a collection of
/// > two to four data (x, y, button 1, button 2). While the Collection item opens a
/// > collection of data, the [MainItem::EndCollection] item closes a collection.
///
#[derive(Debug, Clone, Copy, PartialEq)]
pub enum CollectionItem {
    Physical,
    Application,
    Logical,
    Report,
    NamedArray,
    UsageSwitch,
    UsageModifier,
    Reserved { value: u8 },
    VendorDefined { value: u8 },
}

impl CollectionItem {
    pub fn as_bytes(&self) -> Vec<u8> {
        let data: u8 = match self {
            CollectionItem::Physical => 0x00,
            CollectionItem::Application => 0x01,
            CollectionItem::Logical => 0x02,
            CollectionItem::Report => 0x03,
            CollectionItem::NamedArray => 0x04,
            CollectionItem::UsageSwitch => 0x05,
            CollectionItem::UsageModifier => 0x06,
            CollectionItem::Reserved { value } => *value,
            CollectionItem::VendorDefined { value } => *value,
        };
        vec![0b10100001, data]
    }
}

impl From<CollectionItem> for u8 {
    fn from(c: CollectionItem) -> u8 {
        match c {
            CollectionItem::Physical => 0x00,
            CollectionItem::Application => 0x01,
            CollectionItem::Logical => 0x02,
            CollectionItem::Report => 0x03,
            CollectionItem::NamedArray => 0x04,
            CollectionItem::UsageSwitch => 0x05,
            CollectionItem::UsageModifier => 0x06,
            CollectionItem::Reserved { value } => value,
            CollectionItem::VendorDefined { value } => value,
        }
    }
}

/// See Section 6.2.2.7, a global item applies to all subsequently identified items.
///
/// > Global items describe rather than define data from a control. A new Main item
/// > assumes the characteristics of the item state table. Global items can change the
/// > state table. As a result Global item tags apply to all subsequently defined items
/// > unless overridden by another Global item.
///
/// Note that for convenience the values are converted to `u32` from the HID item
/// they were found in (where they may be represented as `u8`, `u16` or `u32`).
#[derive(Debug, Clone, Copy, PartialEq)]
pub enum GlobalItem {
    UsagePage(UsagePage),
    LogicalMinimum(LogicalMinimum),
    LogicalMaximum(LogicalMaximum),
    PhysicalMinimum(PhysicalMinimum),
    PhysicalMaximum(PhysicalMaximum),
    UnitExponent(UnitExponent),
    Unit(Unit),
    ReportSize(ReportSize),
    ReportId(ReportId),
    ReportCount(ReportCount),
    Push,
    Pop,
    Reserved,
}

impl GlobalItem {
    pub fn as_bytes(&self) -> Vec<u8> {
        let prefix = self.prefix();
        let data: Option<HidBytes> = match self {
            GlobalItem::UsagePage(usage_page) => Some(HidBytes::from(u16::from(usage_page))),
            GlobalItem::LogicalMinimum(min) => Some(HidBytes::from(i32::from(min))),
            GlobalItem::LogicalMaximum(max) => Some(HidBytes::from(i32::from(max))),
            GlobalItem::PhysicalMinimum(min) => Some(HidBytes::from(i32::from(min))),
            GlobalItem::PhysicalMaximum(max) => Some(HidBytes::from(i32::from(max))),
            GlobalItem::UnitExponent(exponent) => Some(HidBytes::from(i32::from(exponent))),
            GlobalItem::Unit(unit) => Some(HidBytes::from(u32::from(unit))),
            GlobalItem::ReportSize(size) => Some(HidBytes::from(usize::from(size))),
            GlobalItem::ReportId(id) => Some(HidBytes::from(u8::from(id))),
            GlobalItem::ReportCount(count) => Some(HidBytes::from(usize::from(count))),
            GlobalItem::Push => None,
            GlobalItem::Pop => None,
            GlobalItem::Reserved => None,
        };
        if let Some(data) = data {
            let len = match data.len() {
                0 => 0b00,
                1 => 0b01,
                2 => 0b10,
                4 => 0b11,
                n => panic!("Invalid data length {n}"),
            };
            [vec![prefix + len], data.take()].concat()
        } else {
            vec![prefix]
        }
    }

    pub fn prefix(&self) -> u8 {
        match self {
            GlobalItem::UsagePage(_) => 0b00000100,
            GlobalItem::LogicalMinimum(_) => 0b00010100,
            GlobalItem::LogicalMaximum(_) => 0b00100100,
            GlobalItem::PhysicalMinimum(_) => 0b00110100,
            GlobalItem::PhysicalMaximum(_) => 0b01000100,
            GlobalItem::UnitExponent(_) => 0b01010100,
            GlobalItem::Unit(_) => 0b01100100,
            GlobalItem::ReportSize(_) => 0b01110100,
            GlobalItem::ReportId(_) => 0b10000100,
            GlobalItem::ReportCount(_) => 0b10010100,
            GlobalItem::Push => 0b10100100,
            GlobalItem::Pop => 0b10110100,
            GlobalItem::Reserved => 0b11000100,
        }
    }
}

/// See Section 6.2.2.8, a local item applies to the current [MainItem].
///
/// > Local item tags define characteristics of controls. These items do not carry over to
/// > the next Main item. If a Main item defines more than one control, it may be
/// > preceded by several similar Local item tags. For example, an Input item may
/// > have several Usage tags associated with it, one for each control.
///
/// Note that the [LocalItem::UsageId] item does not existin the the specification,
/// it is a simplification in this crate. A HID Usage included in a LocalItem
/// may or may not include a Usage Page. Where it does not, this crate uses
/// the [LocalItem::UsageId] instead.
#[derive(Debug, Clone, Copy, PartialEq)]
pub enum LocalItem {
    /// A Usage LocalItem that **does** include a Usage Page, i.e. the
    /// MSB 16 bit component is the Usage Page, the LSB 16 bit component
    /// is the Usage ID.
    Usage(UsagePage, UsageId),
    /// A Usage LocalItem that does **not** include a Usage Page
    UsageId(UsageId),
    UsageMinimum(UsageMinimum),
    UsageMaximum(UsageMaximum),
    DesignatorIndex(DesignatorIndex),
    DesignatorMinimum(DesignatorMinimum),
    DesignatorMaximum(DesignatorMaximum),
    StringIndex(StringIndex),
    StringMinimum(StringMinimum),
    StringMaximum(StringMaximum),
    Delimiter(Delimiter),
    // The value is the value of the upper 6 bits of the first byte,
    // excluding the two lowest size bits (`byte[0] & 0xFC`).
    Reserved {
        value: u8,
    },
}

impl LocalItem {
    pub fn as_bytes(&self) -> Vec<u8> {
        let prefix = self.prefix();
        let data = match self {
            LocalItem::Usage(page, id) => {
                let up: u32 = u16::from(page) as u32;
                let uid: u32 = u16::from(id) as u32;
                let usage = (up << 16) | uid;
                HidBytes::from(usage)
            }
            LocalItem::UsageId(id) => HidBytes::from(u16::from(id)),
            LocalItem::UsageMinimum(min) => HidBytes::from(u32::from(min)),
            LocalItem::UsageMaximum(max) => HidBytes::from(u32::from(max)),
            LocalItem::DesignatorIndex(idx) => HidBytes::from(u32::from(idx)),
            LocalItem::DesignatorMinimum(min) => HidBytes::from(u32::from(min)),
            LocalItem::DesignatorMaximum(max) => HidBytes::from(u32::from(max)),
            LocalItem::StringIndex(idx) => HidBytes::from(u32::from(idx)),
            LocalItem::StringMinimum(min) => HidBytes::from(u32::from(min)),
            LocalItem::StringMaximum(max) => HidBytes::from(u32::from(max)),
            LocalItem::Delimiter(delimiter) => HidBytes::from(u32::from(delimiter)),
            LocalItem::Reserved { value } => HidBytes::from(*value),
        };
        let len = match data.len() {
            0 => 0b00,
            1 => 0b01,
            2 => 0b10,
            4 => 0b11,
            n => panic!("Invalid data length {n}"),
        };
        [vec![prefix + len], data.take()].concat()
    }

    pub fn prefix(&self) -> u8 {
        match self {
            LocalItem::Usage(_, _) => 0b00001000,
            LocalItem::UsageId(_) => 0b00001000,
            LocalItem::UsageMinimum(_) => 0b00011000,
            LocalItem::UsageMaximum(_) => 0b00101000,
            LocalItem::DesignatorIndex(_) => 0b00111000,
            LocalItem::DesignatorMinimum(_) => 0b01001000,
            LocalItem::DesignatorMaximum(_) => 0b01011000,
            LocalItem::StringIndex(_) => 0b01111000,
            LocalItem::StringMinimum(_) => 0b10001000,
            LocalItem::StringMaximum(_) => 0b10011000,
            LocalItem::Delimiter(_) => 0b10101000,
            LocalItem::Reserved { value: _ } => 0b11111000,
        }
    }
}

impl TryFrom<&[u8]> for ItemType {
    type Error = HidError;

    fn try_from(bytes: &[u8]) -> Result<ItemType> {
        ensure!(!bytes.is_empty(), HidError::InsufficientData);
        let itype = (bytes[0] & 0b1100) >> 2;
        match itype {
            0 => Ok(ItemType::Main(MainItem::try_from(bytes)?)),
            1 => Ok(ItemType::Global(GlobalItem::try_from(bytes)?)),
            2 => Ok(ItemType::Local(LocalItem::try_from(bytes)?)),
            3 => Ok(ItemType::Reserved),
            _ => panic!("Item type {itype} cannot happen"),
        }
    }
}

impl TryFrom<&[u8]> for MainItem {
    type Error = HidError;

    fn try_from(bytes: &[u8]) -> Result<MainItem> {
        ensure!(!bytes.is_empty(), HidError::InsufficientData);
        let tag = bytes[0] & 0b11111100;
        match tag {
            0b10000000 => Ok(MainItem::Input(InputItem::try_from(bytes)?)),
            0b10010000 => Ok(MainItem::Output(OutputItem::try_from(bytes)?)),
            0b10110000 => Ok(MainItem::Feature(FeatureItem::try_from(bytes)?)),
            0b10100000 => Ok(MainItem::Collection(CollectionItem::try_from(bytes)?)),
            0b11000000 => Ok(MainItem::EndCollection),
            _ => Err(HidError::InvalidData {
                message: format!("Invalid item tag {tag:#08b}"),
            }),
        }
    }
}

impl TryFrom<&[u8]> for InputItem {
    type Error = HidError;

    fn try_from(bytes: &[u8]) -> Result<Self> {
        ensure!(bytes.len() >= 2, HidError::InsufficientData);
        let data: u32 = HidValue::try_from(&bytes[1..]).unwrap().into();
        Ok(Self {
            is_constant: bit(data, 0),
            is_variable: bit(data, 1),
            is_relative: bit(data, 2),
            wraps: bit(data, 3),
            is_nonlinear: bit(data, 4),
            has_no_preferred_state: bit(data, 5),
            has_null_state: bit(data, 6),
            // InputItem bit 7 is reserved (volatile in output/feature)
            is_buffered_bytes: bit(data, 8),
        })
    }
}

impl TryFrom<&[u8]> for OutputItem {
    type Error = HidError;

    fn try_from(bytes: &[u8]) -> Result<Self> {
        ensure!(bytes.len() >= 2, HidError::InsufficientData);
        let data: u32 = HidValue::try_from(&bytes[1..]).unwrap().into();
        Ok(Self {
            is_constant: bit(data, 0),
            is_variable: bit(data, 1),
            is_relative: bit(data, 2),
            wraps: bit(data, 3),
            is_nonlinear: bit(data, 4),
            has_no_preferred_state: bit(data, 5),
            has_null_state: bit(data, 6),
            is_volatile: bit(data, 7),
            is_buffered_bytes: bit(data, 8),
        })
    }
}

impl TryFrom<&[u8]> for FeatureItem {
    type Error = HidError;

    fn try_from(bytes: &[u8]) -> Result<Self> {
        ensure!(bytes.len() >= 2, HidError::InsufficientData);
        let data: u32 = HidValue::try_from(&bytes[1..]).unwrap().into();
        Ok(Self {
            is_constant: bit(data, 0),
            is_variable: bit(data, 1),
            is_relative: bit(data, 2),
            wraps: bit(data, 3),
            is_nonlinear: bit(data, 4),
            has_no_preferred_state: bit(data, 5),
            has_null_state: bit(data, 6),
            is_volatile: bit(data, 7),
            is_buffered_bytes: bit(data, 8),
        })
    }
}

impl From<&CollectionItem> for u8 {
    fn from(c: &CollectionItem) -> u8 {
        match c {
            CollectionItem::Physical => 0u8,
            CollectionItem::Application => 1u8,
            CollectionItem::Logical => 2u8,
            CollectionItem::Report => 3u8,
            CollectionItem::NamedArray => 4u8,
            CollectionItem::UsageSwitch => 5u8,
            CollectionItem::UsageModifier => 6u8,
            CollectionItem::Reserved { value } => *value,
            CollectionItem::VendorDefined { value } => *value,
        }
    }
}

impl From<u8> for CollectionItem {
    fn from(v: u8) -> CollectionItem {
        match v {
            0x00 => CollectionItem::Physical,
            0x01 => CollectionItem::Application,
            0x02 => CollectionItem::Logical,
            0x03 => CollectionItem::Report,
            0x04 => CollectionItem::NamedArray,
            0x05 => CollectionItem::UsageSwitch,
            0x06 => CollectionItem::UsageModifier,
            value @ 0x07..=0x7f => CollectionItem::Reserved { value },
            value @ 0x80..=0xff => CollectionItem::VendorDefined { value },
        }
    }
}

impl TryFrom<&[u8]> for CollectionItem {
    type Error = HidError;

    fn try_from(bytes: &[u8]) -> Result<CollectionItem> {
        if bytes.len() == 1 {
            return Ok(CollectionItem::Physical);
        }
        match bytes[1] {
            0x00 => Ok(CollectionItem::Physical),
            0x01 => Ok(CollectionItem::Application),
            0x02 => Ok(CollectionItem::Logical),
            0x03 => Ok(CollectionItem::Report),
            0x04 => Ok(CollectionItem::NamedArray),
            0x05 => Ok(CollectionItem::UsageSwitch),
            0x06 => Ok(CollectionItem::UsageModifier),
            value @ 0x07..=0x7f => Ok(CollectionItem::Reserved { value }),
            value @ 0x80..=0xff => Ok(CollectionItem::VendorDefined { value }),
        }
    }
}

impl TryFrom<&[u8]> for GlobalItem {
    type Error = HidError;

    fn try_from(bytes: &[u8]) -> Result<GlobalItem> {
        let value = if bytes.len() >= 2 {
            HidValue::try_from(&bytes[1..]).unwrap()
        } else {
            let v = vec![0u8];
            HidValue::try_from(v.as_slice()).unwrap()
        };
        let item = match bytes[0] & 0b11111100 {
            0b00000100 => GlobalItem::UsagePage(UsagePage(value.into())),
            0b00010100 => GlobalItem::LogicalMinimum(LogicalMinimum(value.into())),
            // Cheating here: we don't know if the data is signed or unsigned
            // unless we look at the LogicalMinimum - but we don't have
            // that here because we're just itemizing, not interpreting.
            // So let's cheat and treat the minimum as signed and the maximum
            // as unsigned which is good enough for anything that doesn't
            // have a LogicalMaximum < 0.
            0b00100100 => GlobalItem::LogicalMaximum(LogicalMaximum(value.into())),
            0b00110100 => GlobalItem::PhysicalMinimum(PhysicalMinimum(value.into())),
            // Cheating here: we don't know if the data is signed or unsigned
            // unless we look at the PhysicalMinimum - but we don't have
            // that here because we're just itemizing, not interpreting.
            // So let's cheat and treat the minimum as signed and the maximum
            // as unsigned which is good enough for anything that doesn't
            // have a PhysicalMaximum < 0.
            0b01000100 => GlobalItem::PhysicalMaximum(PhysicalMaximum(value.into())),
            0b01010100 => GlobalItem::UnitExponent(UnitExponent(value.into())),
            0b01100100 => GlobalItem::Unit(Unit(value.into())),
            0b01110100 => {
                ensure!(bytes.len() >= 2, HidError::InsufficientData);
                GlobalItem::ReportSize(ReportSize(value.into()))
            }
            0b10000100 => {
                ensure!(bytes.len() >= 2, HidError::InsufficientData);
                GlobalItem::ReportId(ReportId(value.into()))
            }
            0b10010100 => {
                ensure!(bytes.len() >= 2, HidError::InsufficientData);
                GlobalItem::ReportCount(ReportCount(value.into()))
            }
            0b10100100 => GlobalItem::Push,
            0b10110100 => GlobalItem::Pop,
            _ => GlobalItem::Reserved,
        };

        Ok(item)
    }
}

impl TryFrom<&[u8]> for LocalItem {
    type Error = HidError;

    fn try_from(bytes: &[u8]) -> Result<LocalItem> {
        ensure!(bytes.len() >= 2, HidError::InsufficientData);
        let value = HidValue::try_from(&bytes[1..]).unwrap();
        let item = match bytes[0] & 0b11111100 {
            0b00001000 => match bytes[1..].len() {
                1 | 2 => LocalItem::UsageId(UsageId(value.into())),
                4 => LocalItem::Usage(
                    UsagePage((u32::from(&value) >> 16) as u16),
                    UsageId(value.into()),
                ),
                n => panic!("Invalid data length {n}"),
            },
            0b00011000 => LocalItem::UsageMinimum(UsageMinimum(value.into())),
            0b00101000 => LocalItem::UsageMaximum(UsageMaximum(value.into())),
            0b00111000 => LocalItem::DesignatorIndex(DesignatorIndex(value.into())),
            0b01001000 => LocalItem::DesignatorMinimum(DesignatorMinimum(value.into())),
            0b01011000 => LocalItem::DesignatorMaximum(DesignatorMaximum(value.into())),
            0b01111000 => LocalItem::StringIndex(StringIndex(value.into())),
            0b10001000 => LocalItem::StringMinimum(StringMinimum(value.into())),
            0b10011000 => LocalItem::StringMaximum(StringMaximum(value.into())),
            0b10101000 => LocalItem::Delimiter(Delimiter(value.into())),
            n => LocalItem::Reserved { value: n },
        };
        Ok(item)
    }
}

// Representation of a raw item in the byte array, see Section 6.2.2.2 and
// 6.2.2.3. Items in a HID report descriptor are represented as short items (1-5 bytes)
// and long items as 3 to 258 bytes.
//
// Note that Section 6.2.2.3 states:
//
// > **Important** No long item tags are defined in this document. These tags are
// > reserved for future use. Tags xF0–xFF are vendor defined.
//
// Support for Long Items in this crate is probably incomplete.
pub trait Item {
    /// The length of this item in bytes, inclusive of the header byte.
    /// For short items this is the length of the data in bytes plus 1 for the header byte.
    /// For long items this is the lengh of the length of the data plus 4 (header byte, data size
    /// byte and 2 bytes for a long item tag).
    fn size(&self) -> usize;

    fn item_type(&self) -> ItemType;
    /// The tag of this item as shifted-down numeric value. For short items this
    /// tag are the upper 4 bits in the header byte shifted down and returned as value in the range
    /// 0..15.
    /// For long items this is the 8-bit long item tag from bytes 2.
    fn tag(&self) -> u8;

    /// The header byte of this item. For short items this
    /// comprises data size, type and tag. For long headers this is a constant
    /// value of 0x7e (see Section 6.2.2.3)
    fn header(&self) -> u8;

    /// Returns true if this item is a Long Item (Section 6.2.2.3). Long items
    /// have a data payload longer than 4 bytes, Short Items (Section 6.2.2.2)
    /// have a data payload of 0, 1, 2 or 4 bytes.
    fn is_long_item(&self) -> bool;

    /// The bytes representing this item as extracted from the report descriptor.
    /// The first byte is the header byte and is guaranteed to exist.
    ///
    /// Note that for convenience this library may expand some values from their u8
    /// representation in the protocol to u32. The bytes here have the original
    /// representation as found in the report descriptor.
    fn bytes(&self) -> &[u8];

    /// Return the item's data bytes, if any.
    fn data(&self) -> Option<ItemData<'_>>;
}

/// Wraps the data bytes of a single [Item].
/// This struct mostly exists for convenience conversations, e.g.
///
///  ```
///  # use crate::hidreport::hid::*;
///  # fn func(item: impl Item) {
///  if let Some(data) = item.data() {
///     let value: u32 = u32::try_from(&data).unwrap();
///  }
///  # }
///  ```
///  and to avoid confusion between [Item::bytes] (all bytes of the HID [Item])
///  and the actual the data bytes).
#[derive(Debug)]
pub struct ItemData<'a> {
    bytes: &'a [u8],
}

impl std::ops::Deref for ItemData<'_> {
    type Target = [u8];

    fn deref(&self) -> &Self::Target {
        self.bytes
    }
}

impl TryFrom<&ItemData<'_>> for u32 {
    type Error = HidError;

    /// Converts the (little endian) data bytes into a u32.
    fn try_from(data: &ItemData) -> Result<u32> {
        ensure!(!data.is_empty(), HidError::InsufficientData);
        match data.len() {
            0 => panic!("Item data with zero bytes must not happen"),
            1 => Ok(data.bytes[0] as u32),
            2 => Ok(u16::from_le_bytes(data.bytes[0..2].try_into().unwrap()) as u32),
            4 => Ok(u32::from_le_bytes(data.bytes[0..4].try_into().unwrap())),
            _ => panic!("Size of {} cannot happen", data.bytes.len()),
        }
    }
}

impl TryFrom<&ItemData<'_>> for u8 {
    type Error = HidError;

    /// Converts the data bytes into a [u8]. This function throws an error if the data length
    /// is larger than 1.
    fn try_from(data: &ItemData) -> Result<u8> {
        ensure!(!data.is_empty(), HidError::InsufficientData);
        match data.len() {
            0 => panic!("Item data with zero bytes must not happen"),
            1 => Ok(data.bytes[0]),
            n @ (2 | 4) => Err(HidError::InvalidData {
                message: format!("Cannot convert {n} bytes to u8"),
            }),
            _ => panic!("Size of {} cannot happen", data.bytes.len()),
        }
    }
}

impl TryFrom<&ItemData<'_>> for Vec<u8> {
    type Error = HidError;

    /// Converts the data bytes into a `Vec<u8>`, copying the data.
    fn try_from(data: &ItemData) -> Result<Vec<u8>> {
        ensure!(!data.is_empty(), HidError::InsufficientData);
        match data.len() {
            0 => panic!("Item data with zero bytes must not happen"),
            3 => panic!("Size of {} cannot happen", data.bytes.len()),
            1..=4 => Ok(data.bytes.to_owned()),
            _ => panic!("Size of {} cannot happen", data.bytes.len()),
        }
    }
}

/// A single item in a parsed (but not yet interpreted) report descriptor.
#[derive(Debug)]
pub struct ReportDescriptorItem {
    offset: usize,
    // FIXME: this needs to support long items once day
    item: ShortItem,
}

impl ReportDescriptorItem {
    /// The offset of this item in the Report Descriptor it was extracted from.
    pub fn offset(&self) -> usize {
        self.offset
    }
    /// The item that is this report descriptor item.
    pub fn item(&self) -> &impl Item {
        &self.item
    }
}

/// A set of items extracted from a report descriptor byte array. This is the
/// result of parsing a report descriptor without *interpreting* it and
/// thus generally only useful to analyze the components of the report descriptor.
#[derive(Debug)]
pub struct ReportDescriptorItems {
    items: Vec<ReportDescriptorItem>,
}

impl std::ops::Deref for ReportDescriptorItems {
    type Target = [ReportDescriptorItem];

    fn deref(&self) -> &Self::Target {
        &self.items
    }
}

impl TryFrom<&[u8]> for ReportDescriptorItems {
    type Error = ParserError;

    /// Attempts to itemize the given HID report descriptor into its
    /// set of [ReportDescriptorItem]s.
    fn try_from(bytes: &[u8]) -> crate::Result<Self> {
        itemize(bytes)
    }
}

#[derive(Debug)]
struct ShortItem {
    item_size: usize,
    header: u8,
    item_type: ItemType,
    bytes: Vec<u8>,
}

impl Item for ShortItem {
    fn is_long_item(&self) -> bool {
        false
    }

    fn size(&self) -> usize {
        self.item_size
    }

    fn item_type(&self) -> ItemType {
        self.item_type
    }

    fn tag(&self) -> u8 {
        (self.header & 0b11110000) >> 4
    }

    fn header(&self) -> u8 {
        self.header
    }

    fn bytes(&self) -> &[u8] {
        &self.bytes
    }

    fn data(&self) -> Option<ItemData<'_>> {
        match self.item_size {
            1 => None,
            2 | 3 | 5 => Some(ItemData {
                bytes: &self.bytes[1..],
            }),
            _ => panic!("Invalid item size {}", self.size()),
        }
    }
}

impl From<&ItemType> for ShortItem {
    fn from(item: &ItemType) -> ShortItem {
        let bytes = item.as_bytes();
        ShortItem::try_from(bytes.as_slice()).unwrap()
    }
}

impl TryFrom<&[u8]> for ShortItem {
    type Error = HidError;

    fn try_from(bytes: &[u8]) -> Result<ShortItem> {
        ensure!(!bytes.is_empty(), HidError::InsufficientData);
        let size = bytes[0] & 0b0011;
        let size = match size {
            0 => 0,
            1 => 1,
            2 => 2,
            3 => 4,
            _ => panic!("Size {size} cannot happen"),
        };
        ensure!(bytes.len() > size, HidError::InsufficientData);
        let itype = ItemType::try_from(&bytes[0..size + 1])?;

        Ok(ShortItem {
            item_size: size + 1,
            item_type: itype,
            header: bytes[0],
            bytes: bytes[0..size + 1].to_owned(),
        })
    }
}

#[derive(Debug, Clone)]
#[allow(dead_code)]
struct LongItem {
    size: usize,
    bytes: Vec<u8>,
}

impl Item for LongItem {
    fn is_long_item(&self) -> bool {
        true
    }

    fn size(&self) -> usize {
        self.size
    }

    fn item_type(&self) -> ItemType {
        ItemType::Long
    }

    fn tag(&self) -> u8 {
        self.bytes[2]
    }

    fn header(&self) -> u8 {
        self.bytes[0]
    }

    fn data(&self) -> Option<ItemData<'_>> {
        Some(ItemData {
            bytes: &self.bytes[3..],
        })
    }

    fn bytes(&self) -> &[u8] {
        &self.bytes
    }
}

impl TryFrom<&[u8]> for LongItem {
    type Error = HidError;

    fn try_from(bytes: &[u8]) -> Result<LongItem> {
        ensure!(bytes.len() >= 3, HidError::InsufficientData);
        if bytes[1] != 0b11111110 {
            return Err(HidError::InvalidData {
                message: "Item is not a long item".into(),
            });
        }
        let size = bytes[1] as usize;

        Ok(LongItem {
            size,
            bytes: bytes[0..size + 3].to_owned(),
        })
    }
}

/// Split the HID Report Descriptor represented by bytes into its set of
/// items.
fn itemize(bytes: &[u8]) -> crate::Result<ReportDescriptorItems> {
    let mut offset = 0;
    let mut items: Vec<ReportDescriptorItem> = Vec::new();
    loop {
        // FIXME: this will break if we ever get long items
        let item = match ShortItem::try_from(&bytes[offset..]) {
            Ok(item) => item,
            Err(e) => {
                return Err(ParserError::InvalidData {
                    offset,
                    message: format!("{e}"),
                });
            }
        };
        let off = offset;
        offset += item.size();
        items.push(ReportDescriptorItem { offset: off, item });
        if offset >= bytes.len() {
            break;
        }
    }
    Ok(ReportDescriptorItems { items })
}

#[doc(hidden)]
pub trait ReportDescriptorBuilderState {}

macro_rules! impl_builder_state {
    ($s:ident) => {
        #[doc(hidden)]
        pub enum $s {}
        impl ReportDescriptorBuilderState for $s {}
    };
}

// Up to 8 collections deep and each collection supports one level of Push/Pop.
// That should be enough for most of the cases we'll see.
impl_builder_state!(ReportDescriptorBuilderToplevel);
impl_builder_state!(ReportDescriptorBuilderC1);
impl_builder_state!(ReportDescriptorBuilderC2);
impl_builder_state!(ReportDescriptorBuilderC3);
impl_builder_state!(ReportDescriptorBuilderC4);
impl_builder_state!(ReportDescriptorBuilderC5);
impl_builder_state!(ReportDescriptorBuilderC6);
impl_builder_state!(ReportDescriptorBuilderC7);
impl_builder_state!(ReportDescriptorBuilderC8);
impl_builder_state!(ReportDescriptorBuilderToplevelPush);
impl_builder_state!(ReportDescriptorBuilderC1Push);
impl_builder_state!(ReportDescriptorBuilderC2Push);
impl_builder_state!(ReportDescriptorBuilderC3Push);
impl_builder_state!(ReportDescriptorBuilderC4Push);
impl_builder_state!(ReportDescriptorBuilderC5Push);
impl_builder_state!(ReportDescriptorBuilderC6Push);
impl_builder_state!(ReportDescriptorBuilderC7Push);
impl_builder_state!(ReportDescriptorBuilderC8Push);

/// A struct for programatically building a HID Report Descriptor.
///
/// ```
/// # use crate::hidreport::hid::*;
/// # use crate::hidreport::types::*;
/// use hut::{self, AsUsage};
///
/// let mut builder = ReportDescriptorBuilder::new();
/// let rdesc: Vec<u8> = builder
///        .usage_page(hut::UsagePage::GenericDesktop)
///        .usage_id(hut::GenericDesktop::Mouse)
///        .open_collection(CollectionItem::Application)
///        .open_collection(CollectionItem::Physical)
///        .push()
///        .append(LogicalMinimum::from(0).into())
///        .append(LogicalMaximum::from(128).into())
///        .pop()
///        .append(ReportCount::from(2).into())
///        .append(ReportSize::from(8).into())
///        .usage_id(hut::GenericDesktop::X)
///        .usage_id(hut::GenericDesktop::Y)
///        .input(ItemBuilder::new()
///               .variable()
///               .absolute()
///               .input())
///        .close_collection()
///        .close_collection()
///        .build();
/// ```
pub struct ReportDescriptorBuilder<S: ReportDescriptorBuilderState> {
    items: Vec<ItemType>,
    // Reassure the compiler that S is used
    marker: std::marker::PhantomData<S>,
}

impl<S: ReportDescriptorBuilderState> ReportDescriptorBuilder<S> {
    /// Append an item to this builder. This will append the necesssary
    /// bytes once [ReportDescriptorBuilder::build()] is called.
    pub fn append(mut self, item: ItemType) -> Self {
        self.items.push(item);
        self
    }

    /// Append the given UsagePage to the report descriptor.
    ///
    /// <div class="warning">
    /// This only appends the Usage Page but not the Usage ID for the
    /// given Usage. This may result in subtle bugs where the Usage Page
    /// differs from the subsequent Usage.
    /// </div>
    ///
    /// However, since most report descriptors seen in the wild use
    /// the [LocalItem::Usage] for the Usage ID only, this wrapper is
    /// provided to make the code more obvious.
    ///
    /// In this **buggy example code** the actual usage used in the report descriptor will be
    /// `GenericDesktop Mouse`.
    ///
    /// <div class="warning">
    /// This example illustrates a bug
    /// </div>
    ///
    /// ```
    /// # use crate::hidreport::hid::*;
    /// use hidreport::types::*;
    /// use hidreport::{Field, ReportDescriptor, Report, VariableField, Usage};
    /// use hut::{self, AsUsagePage, AsUsage};
    ///
    /// let rdesc = ReportDescriptorBuilder::new()
    ///     .usage_page(hut::GenericDesktop::X) // sets Usage Page to GenericDesktop
    ///     .usage_id(hut::Arcade::CoinDoor) // BUG: sets Usage ID to 0x2
    ///     .append(LogicalMinimum::from(0).into())
    ///     .append(LogicalMaximum::from(128).into())
    ///     .append(ReportCount::from(1).into())
    ///     .append(ReportSize::from(8).into())
    ///     .input(ItemBuilder::new()
    ///            .variable()
    ///            .absolute()
    ///           .input())
    ///     .build();
    ///
    ///     let rdesc: ReportDescriptor = ReportDescriptor::try_from(&rdesc).unwrap();
    ///     let input = rdesc.input_reports().first().unwrap();
    ///     let item = input.fields().first().unwrap();
    ///     let usage: Usage = match item {
    ///         Field::Variable(VariableField {
    ///             usage, ..
    ///         }) => *usage,
    ///         _ => panic!("Invalid field type"),
    ///     };
    ///
    ///     let expected_buggy_usage: Usage = hut::GenericDesktop::Mouse.usage().into();
    ///     assert_eq!(usage, expected_buggy_usage);
    /// ```
    ///
    /// This is a convenience wrapper for [Self::append()].
    #[cfg(feature = "hut")]
    pub fn usage_page(self, usage_page: impl hut::AsUsagePage) -> Self {
        let usage_page = usage_page.usage_page();
        self.append(usage_page.into())
    }

    /// Append the given Usage ID to the report descriptor.
    ///
    /// <div class="warning">
    ///  This only appends the Usage ID but not the Usage Page for the given Usage.
    /// This may result in subtle bugs where the Usage Page
    /// differs from the Usage.
    /// </div>
    ///
    /// However, since most report descriptors seen in the wild use
    /// the [LocalItem::Usage] for the Usage ID only, this wrapper is
    /// provided to make the code more obvious.
    ///
    /// In this **buggy example code** the actual usage used in the report descriptor will be
    /// `Button 0x30`.
    ///
    /// <div class="warning">
    /// This example illustrates a bug
    /// </div>
    ///
    /// ```
    /// # use crate::hidreport::hid::*;
    /// use hidreport::types::*;
    /// use hut::{self, AsUsagePage, AsUsage};
    ///
    /// let rdesc = ReportDescriptorBuilder::new()
    ///     .usage_page(hut::UsagePage::Button) // sets Usage Page to Button
    ///     .usage_id(hut::GenericDesktop::X) // BUG: sets Usage ID to 0x30
    ///     .build();
    /// ```
    ///
    /// See [Self::usage_page()] for an more detailed example on a
    /// Usage Page and Usage ID mismatch.
    ///
    /// This is a convenience wrapper for [Self::append()].
    #[cfg(feature = "hut")]
    pub fn usage_id(self, usage: impl hut::AsUsage) -> Self {
        let usage_id: UsageId = usage.usage().into();
        self.append(usage_id.into())
    }

    /// Append the [InputItem]. Use the [ItemBuilder] with [ItemBuilder::input()]
    /// to create this item.
    ///
    /// This is a convenience wrapper for [Self::append()].
    pub fn input(mut self, item: InputItem) -> Self {
        self.items.push(item.into());
        self
    }

    /// Append the [OutputItem]. Use the [ItemBuilder] with [ItemBuilder::output()]
    /// to create this item.
    ///
    /// This is a convenience wrapper for [Self::append()].
    pub fn output(mut self, item: OutputItem) -> Self {
        self.items.push(item.into());
        self
    }

    /// Append the [FeatureItem]. Use the [ItemBuilder] with [ItemBuilder::feature()]
    /// to create this item.
    ///
    /// This is a convenience wrapper for [Self::append()].
    pub fn feature(mut self, item: FeatureItem) -> Self {
        self.items.push(item.into());
        self
    }
}

impl ReportDescriptorBuilder<ReportDescriptorBuilderToplevel> {
    /// Create a new builder
    pub fn new() -> ReportDescriptorBuilder<ReportDescriptorBuilderToplevel> {
        ReportDescriptorBuilder {
            items: Vec::new(),
            marker: std::marker::PhantomData,
        }
    }

    /// Open a new collection for the builder. This collection must be
    /// closed with a call to [close_collection()](Self::close_collection).
    ///
    /// This is a convenience function and identical to
    /// [append()](Self::append) with a [CollectionItem]. However
    /// it enforces that all collections are correctly closed before
    /// [build()](Self::build) can be called.
    pub fn open_collection(
        self,
        item: CollectionItem,
    ) -> ReportDescriptorBuilder<ReportDescriptorBuilderC1> {
        let tmp = self.append(item.into());
        ReportDescriptorBuilder {
            items: tmp.items,
            marker: std::marker::PhantomData,
        }
    }

    /// Pushes the current builder stack (use [pop()](Self::pop)
    /// to return to the current state).
    ///
    /// This is a convenience wrapper for
    /// [append()](Self::append) with a [GlobalItem::Push]. However
    /// it enforces that a `Push` is followed by a `Pop` before
    /// [build()](Self::build) can be called or another collection
    /// can be opened.
    ///
    /// It is not possible to [open_collection()](Self::open_collection) while
    /// in the logical `Push`ed state. This is a restriction by this crate, use
    /// [append()](Self::append) directly where this is required.
    pub fn push(self) -> ReportDescriptorBuilder<ReportDescriptorBuilderToplevelPush> {
        ReportDescriptorBuilder {
            items: self.items,
            marker: std::marker::PhantomData,
        }
    }

    /// Build the report descriptor bytes based on the current builder state.
    ///
    /// This optimizes each HID Items to be of the minimum required, i.e. a value
    /// that fits into a u8 will be encoded as HID Item with a data length of 1, etc.
    ///
    /// This does **not** optimize potentially duplicate fields added by the caller,
    /// e.g. adding two consecutive `ReportSize()` in the builder will result
    /// in both of these showing up in the resulting report descriptor byte array.
    pub fn build(&self) -> Vec<u8> {
        let mut bytes: Vec<u8> = vec![];
        self.items.iter().for_each(|item| {
            let short = ShortItem::from(item);
            bytes.extend(short.bytes());
        });
        bytes
    }
}

impl Default for ReportDescriptorBuilder<ReportDescriptorBuilderToplevel> {
    fn default() -> Self {
        Self::new()
    }
}

impl ReportDescriptorBuilder<ReportDescriptorBuilderToplevelPush> {
    /// Pops the current builder stack, see [push()](ReportDescriptorBuilder::push).
    ///
    /// This is a convenience wrapper for
    /// [append()](Self::append) with a [GlobalItem::Pop]. However
    /// it enforces that a `Push` is followed by a `Pop` before
    /// [build()](Self::build) can be called or another collection
    /// can be opened.
    ///
    /// It is not possible to [open_collection()](Self::open_collection) while
    /// in the logical `Push`ed state. This is a restriction by this crate, use
    /// [append()](Self::append) directly where this is required.
    pub fn pop(self) -> ReportDescriptorBuilder<ReportDescriptorBuilderToplevel> {
        ReportDescriptorBuilder {
            items: self.items,
            marker: std::marker::PhantomData,
        }
    }
}

impl ReportDescriptorBuilder<ReportDescriptorBuilderC1> {
    /// Close the current collection.
    ///
    /// This function is only available after [open_collection()](Self::open_collection).
    pub fn close_collection(self) -> ReportDescriptorBuilder<ReportDescriptorBuilderToplevel> {
        let tmp = self.append(MainItem::EndCollection.into());
        ReportDescriptorBuilder {
            items: tmp.items,
            marker: std::marker::PhantomData,
        }
    }
}

macro_rules! impl_open_collection {
    ($cb:ty, $cc:ty) => {
        impl ReportDescriptorBuilder<$cb> {
            #[doc(hidden)]
            pub fn open_collection(self, item: CollectionItem) -> ReportDescriptorBuilder<$cc> {
                let tmp = self.append(item.into());
                ReportDescriptorBuilder {
                    items: tmp.items,
                    marker: std::marker::PhantomData,
                }
            }
        }
    };
}

macro_rules! impl_close_collection {
    ($ca:ty, $cb:ty) => {
        impl ReportDescriptorBuilder<$cb> {
            #[doc(hidden)]
            pub fn close_collection(self) -> ReportDescriptorBuilder<$ca> {
                let tmp = self.append(MainItem::EndCollection.into());
                ReportDescriptorBuilder {
                    items: tmp.items,
                    marker: std::marker::PhantomData,
                }
            }
        }
    };
}

impl_open_collection!(ReportDescriptorBuilderC1, ReportDescriptorBuilderC2);
impl_open_collection!(ReportDescriptorBuilderC2, ReportDescriptorBuilderC3);
impl_open_collection!(ReportDescriptorBuilderC3, ReportDescriptorBuilderC4);
impl_open_collection!(ReportDescriptorBuilderC4, ReportDescriptorBuilderC5);
impl_open_collection!(ReportDescriptorBuilderC5, ReportDescriptorBuilderC6);
impl_open_collection!(ReportDescriptorBuilderC6, ReportDescriptorBuilderC7);
impl_open_collection!(ReportDescriptorBuilderC7, ReportDescriptorBuilderC8);
impl_close_collection!(ReportDescriptorBuilderC1, ReportDescriptorBuilderC2);
impl_close_collection!(ReportDescriptorBuilderC2, ReportDescriptorBuilderC3);
impl_close_collection!(ReportDescriptorBuilderC3, ReportDescriptorBuilderC4);
impl_close_collection!(ReportDescriptorBuilderC4, ReportDescriptorBuilderC5);
impl_close_collection!(ReportDescriptorBuilderC5, ReportDescriptorBuilderC6);
impl_close_collection!(ReportDescriptorBuilderC6, ReportDescriptorBuilderC7);

macro_rules! impl_builder_for_push {
    ($ca:ty, $cb:ty) => {
        impl ReportDescriptorBuilder<$ca> {
            #[doc(hidden)]
            pub fn push(self) -> ReportDescriptorBuilder<$cb> {
                let tmp = self.append(GlobalItem::Push.into());
                ReportDescriptorBuilder {
                    items: tmp.items,
                    marker: std::marker::PhantomData,
                }
            }
        }
        impl ReportDescriptorBuilder<$cb> {
            #[doc(hidden)]
            pub fn pop(self) -> ReportDescriptorBuilder<$ca> {
                let tmp = self.append(GlobalItem::Pop.into());
                ReportDescriptorBuilder {
                    items: tmp.items,
                    marker: std::marker::PhantomData,
                }
            }
        }
    };
}

impl_builder_for_push!(ReportDescriptorBuilderC1, ReportDescriptorBuilderC1Push);
impl_builder_for_push!(ReportDescriptorBuilderC2, ReportDescriptorBuilderC2Push);
impl_builder_for_push!(ReportDescriptorBuilderC3, ReportDescriptorBuilderC3Push);
impl_builder_for_push!(ReportDescriptorBuilderC4, ReportDescriptorBuilderC4Push);
impl_builder_for_push!(ReportDescriptorBuilderC5, ReportDescriptorBuilderC5Push);
impl_builder_for_push!(ReportDescriptorBuilderC6, ReportDescriptorBuilderC6Push);

#[cfg(test)]
mod tests {
    use super::*;
    use crate::{Field, Report, ReportDescriptor, Usage, VariableField};
    use hut::{self, AsUsage};

    #[test]
    fn item_size() {
        for size in 1..4 {
            let itype = 0b100; // Global
            let tag = 0b00010000; // Logical Minimum
            let bytes: [u8; 5] = [tag | itype | size, 1, 2, 3, 4];
            let bytes = bytes.as_slice();

            let item = ShortItem::try_from(bytes).unwrap();
            match size {
                0 => assert_eq!(item.size(), 1),
                1 => assert_eq!(item.size(), 2),
                2 => assert_eq!(item.size(), 3),
                3 => assert_eq!(item.size(), 5),
                _ => panic!("Size {size} cannot happen"),
            }
        }
    }

    #[test]
    fn item_type() {
        let itype = 0b10010000; // Output
        let size = 3;
        let bytes: [u8; 5] = [itype | size, 0b10101010, 0b1, 0, 0];
        let bytes = bytes.as_slice();

        let item = ShortItem::try_from(bytes).unwrap();
        assert!(matches!(item.item_type(), ItemType::Main { .. }));
        match item.item_type() {
            ItemType::Main(mi) => match mi {
                MainItem::Output(o) => match o {
                    _ => {
                        assert!(o.is_constant == false);
                        assert!(o.is_variable == true);
                        assert!(o.is_relative == false);
                        assert!(o.wraps == true);
                        assert!(o.is_nonlinear == false);
                        assert!(o.has_no_preferred_state == true);
                        assert!(o.has_null_state == false);
                        assert!(o.is_volatile == true);
                        assert!(o.is_buffered_bytes == true);
                    }
                },
                _ => panic!("Failed match against MainItem"),
            },
            _ => panic!("Wrong item type"),
        }
    }

    #[test]
    fn item_data() {
        let bytes = [1, 2, 3, 4, 5];
        let item_data = ItemData { bytes: &bytes[..1] };
        assert_eq!(u32::try_from(&item_data).unwrap(), 1);
        let item_data = ItemData { bytes: &bytes[..2] };
        assert_eq!(u32::try_from(&item_data).unwrap(), 0x0201);
        let item_data = ItemData { bytes: &bytes[..4] };
        assert_eq!(u32::try_from(&item_data).unwrap(), 0x04030201);
    }

    macro_rules! test_hid_value {
        ($bytes:expr, $unsigned:expr, $signed:expr) => {
            let v = HidValue::try_from($bytes.as_slice()).unwrap();
            assert_eq!(u32::from(&v), $unsigned);
            if ($bytes.len() <= 2) {
                assert!($unsigned as u32 <= 0xFFFFu32);
                assert_eq!(u16::from(&v), $unsigned as u16);
            }
            if ($bytes.len() <= 1) {
                assert!($unsigned as u32 <= 0xFFu32);
                assert_eq!(u8::from(&v), $unsigned as u8);
            }
            assert_eq!(i32::from(&v), $signed);
        };
    }

    #[test]
    fn hid_value() {
        test_hid_value!([0x1, 0x2, 0x3, 0x4], 0x04030201u32, 0x04030201);

        test_hid_value!([0x7F], 0x7F, 127);
        test_hid_value!([0x80], 0x80, -128);
        test_hid_value!([0xFF], 0xFF, -1);
        test_hid_value!([0x0], 0x0, 0);
        test_hid_value!([0x1], 0x1, 1);

        test_hid_value!([0xFF, 0x7F], 0x7FFFu32, 32767); // max positive i16
        test_hid_value!([0x00, 0x80], 0x8000u32, -32768); // min i16
        test_hid_value!([0xFF, 0xFF], 0xFFFFu32, -1); // -1
        test_hid_value!([0x01, 0x00], 0x0001u32, 1); // small positive
        test_hid_value!([0x34, 0x12], 0x1234u32, 4660); // mid-range positive
        test_hid_value!([0xCC, 0xED], 0xEDCCu32, -4660); // mid-range negative
        test_hid_value!([0x00, 0x00], 0x0000u32, 0); // zero

        // 4-byte signed values
        test_hid_value!([0xFF, 0xFF, 0xFF, 0x7F], 0x7FFFFFFFu32, 2147483647); // max positive i32
        test_hid_value!([0x00, 0x00, 0x00, 0x80], 0x80000000u32, -2147483648); // min i32
        test_hid_value!([0xFF, 0xFF, 0xFF, 0xFF], 0xFFFFFFFFu32, -1); // -1
        test_hid_value!([0x01, 0x00, 0x00, 0x00], 0x00000001u32, 1); // small positive
        test_hid_value!([0x78, 0x56, 0x34, 0x12], 0x12345678u32, 305419896); // mid-range positive
        test_hid_value!([0x88, 0xA9, 0xCB, 0xED], 0xEDCBA988u32, -305419896); // mid-range negative
        test_hid_value!([0x00, 0x00, 0x00, 0x00], 0x00000000u32, 0); // zero
    }

    #[test]
    fn hidbytes() {
        let bytes = HidBytes::from(1u8).take();
        assert_eq!(bytes, [0x1]);
        let bytes = HidBytes::from(1u16).take();
        assert_eq!(bytes, [0x1]);
        let bytes = HidBytes::from(1u32).take();
        assert_eq!(bytes, [0x1]);

        let bytes = HidBytes::from(255u8).take();
        assert_eq!(bytes, [0xff]);
        let bytes = HidBytes::from(255u16).take();
        assert_eq!(bytes, [0xff]);
        let bytes = HidBytes::from(255u32).take();
        assert_eq!(bytes, [0xff]);

        // >=128 signed is encoded over two bytes. That's not
        // always necessary but whether a value is signed or
        // unsigned (e.g. LogicalMaximum) is only known after
        // parsing the minmimum.
        let bytes = HidBytes::from(128i16).take();
        assert_eq!(bytes, [0x80, 0x0]);
        let bytes = HidBytes::from(128i32).take();
        assert_eq!(bytes, [0x80, 0x0]);
        let bytes = HidBytes::from(255i16).take();
        assert_eq!(bytes, [0xff, 0x0]);
        let bytes = HidBytes::from(255i32).take();
        assert_eq!(bytes, [0xff, 0x0]);

        let bytes = HidBytes::from(256u16).take();
        assert_eq!(bytes, [0x0, 0x1]);
        let bytes = HidBytes::from(256u32).take();
        assert_eq!(bytes, [0x0, 0x1]);

        let bytes = HidBytes::from(0x10000u32).take();
        assert_eq!(bytes, [0x0, 0x0, 0x1, 0x0]);
        let bytes = HidBytes::from(0x1000000u32).take();
        assert_eq!(bytes, [0x0, 0x0, 0x0, 0x1]);
        let bytes = HidBytes::from(u32::MAX).take();
        assert_eq!(bytes, [0xff, 0xff, 0xff, 0xff]);

        let bytes = HidBytes::from(-1i8).take();
        assert_eq!(bytes, [0xff]);
        let bytes = HidBytes::from(-1i16).take();
        assert_eq!(bytes, [0xff]);
        let bytes = HidBytes::from(-1i32).take();
        assert_eq!(bytes, [0xff]);

        let bytes = HidBytes::from(i16::MAX - 1).take();
        assert_eq!(bytes, [0xfe, 0x7f]);
        let bytes = HidBytes::from(i32::MAX - 1).take();
        assert_eq!(bytes, [0xfe, 0xff, 0xff, 0x7f]);
    }

    #[test]
    fn builder_example() {
        let builder = ReportDescriptorBuilder::new();
        let rdesc: Vec<u8> = builder
            .usage_page(hut::UsagePage::GenericDesktop)
            .usage_id(hut::GenericDesktop::Mouse)
            .open_collection(CollectionItem::Application)
            .open_collection(CollectionItem::Physical)
            .push()
            .append(LogicalMinimum::from(0).into())
            .append(LogicalMaximum::from(128).into())
            .pop()
            .append(ReportCount::from(2).into())
            .append(ReportSize::from(8).into())
            .usage_id(hut::GenericDesktop::X)
            .usage_id(hut::GenericDesktop::Y)
            .input(ItemBuilder::new().variable().absolute().input())
            .close_collection()
            .close_collection()
            .build();

        #[rustfmt::skip]
        let expected_bytes = [
            0x05, 0x01,                    // Usage Page (Generic Desktop)
            0x09, 0x02,                    // Usage (Mouse)
            0xa1, 0x01,                    // Collection (Application)
            0xa1, 0x00,                    //   Collection (Application)
            0xa4,                          //     Push
            0x15, 0x00,                    //       Logical Minimum (0)
            0x26, 0x80, 0x00,              //       Logical Maximum (128)
            0xb4,                          //     Pop
            0x95, 0x02,                    //     Report Count (1)
            0x75, 0x08,                    //     Report Size (8)
            0x09, 0x30,                    //     Usage (X)
            0x09, 0x31,                    //     Usage (Y)
            0x81, 0x02,                    //     Input (Data,Var,Abs)
            0xc0,                          //   End Collection
            0xc0,                          // End Collection
        ];
        assert_eq!(rdesc, expected_bytes);
    }

    #[test]
    fn builder_buggy_usages() {
        let rdesc = ReportDescriptorBuilder::new()
            .usage_page(hut::GenericDesktop::X) // sets Usage Page to GenericDesktop
            .usage_id(hut::Arcade::CoinDoor) // sets Usage ID to 0x2
            .append(LogicalMinimum::from(0).into())
            .append(LogicalMaximum::from(128).into())
            .append(ReportCount::from(2).into())
            .append(ReportSize::from(8).into())
            .input(ItemBuilder::new().variable().absolute().input())
            .build();

        let rdesc: ReportDescriptor = ReportDescriptor::try_from(&rdesc).unwrap();
        let input = rdesc.input_reports().first().unwrap();
        let item = input.fields().first().unwrap();
        let usage: Usage = match item {
            Field::Variable(VariableField { usage, .. }) => *usage,
            _ => panic!("Invalid field type"),
        };

        let expected_buggy_usage: Usage = hut::GenericDesktop::Mouse.usage().into();
        assert_eq!(usage, expected_buggy_usage);
    }

    #[test]
    fn builder() {
        // recorded from a Microsoft Microsoft® 2.4GHz Transceiver v9.0
        // This device uses 2-bytes for UsageMinimum/maximu even if <256 so those entries are
        // modified here to match our builder behavior which squishes those into a single
        // byte if possible.
        #[rustfmt::skip]
        let expected_bytes = [
            0x05, 0x01,                    // Usage Page (Generic Desktop)              0
            0x09, 0x06,                    // Usage (Keyboard)                          2
            0xa1, 0x01,                    // Collection (Application)                  4
            0x05, 0x08,                    //   Usage Page (LED)                        6
            0x19, 0x01,                    //   UsageMinimum (1)                        8
            0x29, 0x03,                    //   UsageMaximum (3)                        10
            0x15, 0x00,                    //   Logical Minimum (0)                     12
            0x25, 0x01,                    //   Logical Maximum (1)                     14
            0x75, 0x01,                    //   Report Size (1)                         16
            0x95, 0x03,                    //   Report Count (3)                        18
            0x91, 0x02,                    //   Output (Data,Var,Abs)                   20
            0x95, 0x05,                    //   Report Count (5)                        22
            0x91, 0x01,                    //   Output (Cnst,Arr,Abs)                   24
            0x05, 0x07,                    //   Usage Page (Keyboard/Keypad)            26
            0x19, 0xe0, /* 0x1a, 0xe0, 0x00, */ //   UsageMinimum (224)                      28
            0x29, 0xe7, /* 0x2a, 0xe7, 0x00, */ //   UsageMaximum (231)                      31
            0x95, 0x08,                    //   Report Count (8)                        34
            0x81, 0x02,                    //   Input (Data,Var,Abs)                    36
            0x75, 0x08,                    //   Report Size (8)                         38
            0x95, 0x01,                    //   Report Count (1)                        40
            0x81, 0x01,                    //   Input (Cnst,Arr,Abs)                    42
            0x19, 0x00,                    //   UsageMinimum (0)                        44
            0x29, 0x91, /* 0x2a, 0x91, 0x00, */ //   UsageMaximum (145)                      46
            0x26, 0xff, 0x00,              //   Logical Maximum (255)                   49
            0x95, 0x06,                    //   Report Count (6)                        52
            0x81, 0x00,                    //   Input (Data,Arr,Abs)                    54
            0x05, 0x0c,                    //   Usage Page (Consumer)                   56
            0x0a, 0xc0, 0x02,              //   Usage (Extended Keyboard Attributes Collection) 58
            0xa1, 0x02,                    //   Collection (Logical)                    61
            0x1a, 0xc1, 0x02,              //     UsageMinimum (705)                    63
            0x2a, 0xc6, 0x02,              //     UsageMaximum (710)                    66
            0x95, 0x06,                    //     Report Count (6)                      69
            0xb1, 0x03,                    //     Feature (Cnst,Var,Abs)                71
            0xc0,                          //   End Collection                          73
            0xc0,                          // End Collection                            74
        ];
        let builder = ReportDescriptorBuilder::new();
        let rdesc: Vec<u8> = builder
            .append(hut::UsagePage::GenericDesktop.into())
            .append(UsageId::from(hut::GenericDesktop::Keyboard.usage()).into())
            .open_collection(CollectionItem::Application)
            .append(hut::UsagePage::LED.into())
            .append(UsageMinimum(1).into())
            .append(UsageMaximum(3).into())
            .append(LogicalMinimum(0).into())
            .append(LogicalMaximum(1).into())
            .append(ReportSize(1).into())
            .append(ReportCount(3).into())
            .output(ItemBuilder::new().data().variable().absolute().output())
            .append(ReportCount(5).into())
            .output(ItemBuilder::new().constant().array().absolute().output())
            .append(hut::UsagePage::KeyboardKeypad.into())
            .append(UsageMinimum(224).into())
            .append(UsageMaximum(231).into())
            .append(ReportCount(8).into())
            .input(ItemBuilder::new().data().variable().absolute().input())
            .append(ReportSize(8).into())
            .append(ReportCount(1).into())
            .input(ItemBuilder::new().constant().array().absolute().input())
            .append(UsageMinimum(0).into())
            .append(UsageMaximum(145).into())
            .append(LogicalMaximum(255).into())
            .append(ReportCount(6).into())
            .input(ItemBuilder::new().data().array().absolute().input())
            .append(hut::UsagePage::Consumer.into())
            .append(
                UsageId::from(hut::Consumer::ExtendedKeyboardAttributesCollection.usage()).into(),
            )
            .open_collection(CollectionItem::Logical)
            .append(UsageMinimum(705).into())
            .append(UsageMaximum(710).into())
            .append(ReportCount(6).into())
            .feature(
                ItemBuilder::new()
                    .constant()
                    .variable()
                    .absolute()
                    .feature(),
            )
            .close_collection()
            .close_collection()
            .build();
        assert_eq!(rdesc, expected_bytes);
    }
}
