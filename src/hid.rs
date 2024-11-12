// SPDX-License-Identifier: MIT

//! A wrapper around the HID Core items. This module handles splitting
//! a report descriptor byte stream into its individual components.
//! Interpretation and/or analysis of the resulting [Item]s is left to
//! the caller.
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
//! In this document and unless stated otherwise, a reference to "Section a.b.c" refers to the
//! [HID Device Class Definition for HID 1.11](https://www.usb.org/document-library/device-class-definition-hid-111).

use crate::types::*;
use crate::{ensure, ParserError};

use thiserror::Error;

/// Convenience function to be extract a single bit as bool from a value
fn bit(bits: u32, bit: u8) -> bool {
    assert!(bit < 32);
    bits & (1 << bit) != 0
}

/// Convenience function to extract the bytes into a u32
pub(crate) fn hiddata(bytes: &[u8]) -> Option<u32> {
    match bytes.len() {
        0 => None,
        1 => Some(bytes[0] as u32),
        2 => Some(u16::from_le_bytes(bytes[0..2].try_into().unwrap()) as u32),
        4 => Some(u32::from_le_bytes(bytes[0..4].try_into().unwrap())),
        _ => panic!("Size {} cannot happen", bytes.len()),
    }
}

/// Convenience function to extract the bytes into a i32
pub(crate) fn hiddata_signed(bytes: &[u8]) -> Option<i32> {
    match bytes.len() {
        0 => None,
        1 => Some((bytes[0] as i8) as i32),
        2 => Some(i16::from_le_bytes(bytes[0..2].try_into().unwrap()) as i32),
        4 => Some(i32::from_le_bytes(bytes[0..4].try_into().unwrap())),
        _ => panic!("Size {} cannot happen", bytes.len()),
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
#[derive(Debug, Clone, Copy)]
pub enum ItemType {
    Main(MainItem),
    Global(GlobalItem),
    Local(LocalItem),
    Long,
    Reserved,
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
#[derive(Debug, Clone, Copy)]
pub enum MainItem {
    Input(InputItem),
    Output(OutputItem),
    Feature(FeatureItem),
    Collection(CollectionItem),
    EndCollection,
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
#[derive(Debug, Clone, Copy)]
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

/// See Section 6.2.2.5. Equivalent to the [InputItem], please
/// refer to that documentation.
///
/// The only difference to the [InputItem] is the existence of the
/// the [OutputItem::is_volatile].
#[derive(Debug, Clone, Copy)]
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

    pub fn is_non_volatile(&self) -> bool {
        !self.is_volatile()
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
#[derive(Debug, Clone, Copy)]
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
    pub fn is_non_volatile(&self) -> bool {
        !self.is_volatile()
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

/// See Section 6.2.2.7, a global item applies to all subsequently identified items.
///
/// > Global items describe rather than define data from a control. A new Main item
/// > assumes the characteristics of the item state table. Global items can change the
/// > state table. As a result Global item tags apply to all subsequently defined items
/// > unless overridden by another Global item.
///
/// Note that for convenience the values are converted to `u32` from the HID item
/// they were found in (where they may be represented as `u8`, `u16` or `u32`).
#[derive(Debug, Clone, Copy)]
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
#[derive(Debug, Clone, Copy)]
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
                message: format!("Invalid item tag {tag}"),
            }),
        }
    }
}

impl TryFrom<&[u8]> for InputItem {
    type Error = HidError;

    fn try_from(bytes: &[u8]) -> Result<Self> {
        ensure!(bytes.len() >= 2, HidError::InsufficientData);
        let data = hiddata(&bytes[1..]).unwrap();
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
        let data = hiddata(&bytes[1..]).unwrap();
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
        let data = hiddata(&bytes[1..]).unwrap();
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
        let (data, data_signed) = if bytes.len() >= 2 {
            (hiddata(&bytes[1..]), hiddata_signed(&bytes[1..]))
        } else {
            (Some(0), Some(0))
        };
        let item = match bytes[0] & 0b11111100 {
            0b00000100 => GlobalItem::UsagePage(UsagePage(data.unwrap() as u16)),
            0b00010100 => GlobalItem::LogicalMinimum(LogicalMinimum(data_signed.unwrap())),
            // Cheating here: we don't know if the data is signed or unsigned
            // unless we look at the LogicalMinimum - but we don't have
            // that here because we're just itemizing, not interpreting.
            // So let's cheat and treat the minimum as signed and the maximum
            // as unsigned which is good enough for anything that doesn't
            // have a LogicalMaximum < 0.
            0b00100100 => GlobalItem::LogicalMaximum(LogicalMaximum(data.unwrap() as i32)),
            0b00110100 => GlobalItem::PhysicalMinimum(PhysicalMinimum(data_signed.unwrap())),
            // Cheating here: we don't know if the data is signed or unsigned
            // unless we look at the PhysicalMinimum - but we don't have
            // that here because we're just itemizing, not interpreting.
            // So let's cheat and treat the minimum as signed and the maximum
            // as unsigned which is good enough for anything that doesn't
            // have a PhysicalMaximum < 0.
            0b01000100 => GlobalItem::PhysicalMaximum(PhysicalMaximum(data.unwrap() as i32)),
            0b01010100 => GlobalItem::UnitExponent(UnitExponent(data.unwrap())),
            0b01100100 => GlobalItem::Unit(Unit(data.unwrap())),
            0b01110100 => {
                ensure!(bytes.len() >= 2, HidError::InsufficientData);
                GlobalItem::ReportSize(ReportSize(data.unwrap() as usize))
            }
            0b10000100 => {
                ensure!(bytes.len() >= 2, HidError::InsufficientData);
                GlobalItem::ReportId(ReportId(data.unwrap() as u8))
            }
            0b10010100 => {
                ensure!(bytes.len() >= 2, HidError::InsufficientData);
                GlobalItem::ReportCount(ReportCount(data.unwrap() as usize))
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
        let data = hiddata(&bytes[1..]);
        let item = match bytes[0] & 0b11111100 {
            0b00001000 => match bytes[1..].len() {
                1 | 2 => LocalItem::UsageId(UsageId(data.unwrap() as u16)),
                4 => LocalItem::Usage(
                    UsagePage((data.unwrap() >> 16) as u16),
                    UsageId((data.unwrap() & 0xFFFF) as u16),
                ),
                n => panic!("Invalid data length {n}"),
            },
            0b00011000 => LocalItem::UsageMinimum(UsageMinimum(data.unwrap())),
            0b00101000 => LocalItem::UsageMaximum(UsageMaximum(data.unwrap())),
            0b00111000 => LocalItem::DesignatorIndex(DesignatorIndex(data.unwrap())),
            0b01001000 => LocalItem::DesignatorMinimum(DesignatorMinimum(data.unwrap())),
            0b01011000 => LocalItem::DesignatorMaximum(DesignatorMaximum(data.unwrap())),
            0b01111000 => LocalItem::StringIndex(StringIndex(data.unwrap())),
            0b10001000 => LocalItem::StringMinimum(StringMinimum(data.unwrap())),
            0b10011000 => LocalItem::StringMaximum(StringMaximum(data.unwrap())),
            0b10101000 => LocalItem::Delimiter(Delimiter(data.unwrap())),
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
    fn data(&self) -> Option<ItemData>;
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

impl<'a> std::ops::Deref for ItemData<'a> {
    type Target = [u8];

    fn deref(&self) -> &Self::Target {
        self.bytes
    }
}

impl<'a> TryFrom<&ItemData<'a>> for u32 {
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

impl<'a> TryFrom<&ItemData<'a>> for u8 {
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

impl<'a> TryFrom<&ItemData<'a>> for Vec<u8> {
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

    fn data(&self) -> Option<ItemData> {
        match self.item_size {
            1 => None,
            2 | 3 | 5 => Some(ItemData {
                bytes: &self.bytes[1..],
            }),
            _ => panic!("Invalid item size {}", self.size()),
        }
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

    fn data(&self) -> Option<ItemData> {
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

#[cfg(test)]
mod tests {
    use super::*;

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
}
