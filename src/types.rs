// SPDX-License-Identifier: MIT

//! A collection of standalone HID types that exist for type safety only.
//! These are all simple wrappers around their underlying integer data type.
//!
//! In this document and unless stated otherwise, a reference to "Section a.b.c" refers to the
//! [HID Device Class Definition for HID 1.11](https://www.usb.org/document-library/device-class-definition-hid-111).

/// Creates a `From<Foo> for u32` and `From<u32> for Foo` implementation for the given `Foo` type.
/// Use like this: `impl_from(Foo, Foo, u32)`.
macro_rules! impl_from {
    ($tipo:ty, $tipo_expr:expr, $to:ty) => {
        impl From<$tipo> for $to {
            fn from(f: $tipo) -> $to {
                f.0
            }
        }
        impl From<&$tipo> for $to {
            fn from(f: &$tipo) -> $to {
                f.0
            }
        }
        impl From<$to> for $tipo {
            fn from(f: $to) -> Self {
                $tipo_expr(f)
            }
        }
    };
}

macro_rules! impl_asref {
    ($tipo:ty) => {
        impl AsRef<$tipo> for $tipo {
            #[inline(always)]
            fn as_ref(&self) -> &$tipo {
                self
            }
        }
    };
}

/// Creates a `impl Display for Foo` that just converts into the underlying number.
/// Use like this: `impl_fmt(Foo, u32)`.
macro_rules! impl_fmt {
    ($tipo:ty, $to:ty) => {
        impl std::fmt::Display for $tipo {
            fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
                let v: $to = self.into();
                write!(f, "{v}")
            }
        }
    };
}

// ---------- GLOBAL ITEMS ---------------------
#[derive(Debug, Clone, Copy)]
pub struct UsagePage(pub u16);

impl_from!(UsagePage, UsagePage, u16);
impl_fmt!(UsagePage, u16);

#[derive(Debug, Clone, Copy, PartialEq, PartialOrd)]
pub struct LogicalMinimum(pub i32);

impl_from!(LogicalMinimum, LogicalMinimum, i32);
impl_fmt!(LogicalMinimum, i32);

#[derive(Debug, Clone, Copy, PartialEq, PartialOrd)]
pub struct LogicalMaximum(pub i32);

impl_from!(LogicalMaximum, LogicalMaximum, i32);
impl_fmt!(LogicalMaximum, i32);

#[derive(Debug, Clone, Copy, PartialEq, PartialOrd)]
pub struct PhysicalMinimum(pub i32);

impl_from!(PhysicalMinimum, PhysicalMinimum, i32);
impl_fmt!(PhysicalMinimum, i32);

#[derive(Debug, Clone, Copy, PartialEq, PartialOrd)]
pub struct PhysicalMaximum(pub i32);

impl_from!(PhysicalMaximum, PhysicalMaximum, i32);
impl_fmt!(PhysicalMaximum, i32);

#[derive(Debug, Clone, Copy)]
pub enum UnitSystem {
    None,
    SILinear,
    SIRotation,
    EnglishLinear,
    EnglishRotation,
}

#[derive(Debug, Clone, Copy)]
pub enum Units {
    None,
    Centimeter,
    Radians,
    Inch,
    Degrees,
    Gram,
    Slug,
    Seconds,
    Kelvin,
    Fahrenheit,
    Ampere,
    Candela,
}

#[derive(Debug, Clone, Copy)]
pub struct Unit(pub u32);

impl_from!(Unit, Unit, u32);
impl_fmt!(Unit, u32);

impl Unit {
    fn nibbles(&self) -> Vec<u8> {
        std::ops::Range { start: 0, end: 32 }
            .step_by(4)
            .map(|shift| ((self.0 & (0b1111 << shift)) >> shift) as u8)
            .collect()
    }

    /// Returns all units set by this field that are not [Units::None].
    /// If all units are [Units::None], the return value is [None], any
    /// [Some] contains a vector with at least one element.
    pub fn units(&self) -> Option<Vec<Units>> {
        let units: Vec<Units> = vec![
            self.length(),
            self.mass(),
            self.time(),
            self.temperature(),
            self.current(),
            self.luminosity(),
        ]
        .into_iter()
        .filter(|u| !matches!(u, Units::None))
        .collect();

        if units.is_empty() {
            None
        } else {
            Some(units)
        }
    }

    /// The [UnitSystem] used by a field.
    /// Returns [UnitSystem::None] if unset.
    pub fn system(&self) -> UnitSystem {
        match self.nibbles().first() {
            None | Some(0) => UnitSystem::None,
            Some(1) => UnitSystem::SILinear,
            Some(2) => UnitSystem::SIRotation,
            Some(3) => UnitSystem::EnglishLinear,
            Some(4) => UnitSystem::EnglishRotation,
            Some(n) => panic!("invalid size {n} for a nibble"),
        }
    }

    /// The length, one of [Units::Centimeter], [Units::Radians], [Units::Inch]
    /// or [Units::Degrees].
    /// Returns [Units::None] if unset.
    pub fn length(&self) -> Units {
        match self.nibbles().get(1) {
            None | Some(0) => Units::None,
            Some(1) => Units::Centimeter,
            Some(2) => Units::Radians,
            Some(3) => Units::Inch,
            Some(4) => Units::Degrees,
            Some(n) => panic!("invalid size {n} for a nibble"),
        }
    }

    /// The mass, one of [Units::Gram] or [Units::Slug].
    /// Returns [Units::None] if unset.
    pub fn mass(&self) -> Units {
        match self.nibbles().get(2) {
            None | Some(0) => Units::None,
            Some(1) => Units::Gram,
            Some(2) => Units::Gram,
            Some(3) => Units::Slug,
            Some(4) => Units::Slug,
            Some(n) => panic!("invalid size {n} for a nibble"),
        }
    }

    /// The time, one of [Units::Seconds].
    /// Returns [Units::None] if unset.
    pub fn time(&self) -> Units {
        match self.nibbles().get(2) {
            None | Some(0) => Units::None,
            Some(1..=4) => Units::Seconds,
            Some(n) => panic!("invalid size {n} for a nibble"),
        }
    }

    /// The time, one of [Units::Kelvin] or [Units::Fahrenheit].
    /// Returns [Units::None] if unset.
    pub fn temperature(&self) -> Units {
        match self.nibbles().get(3) {
            None | Some(0) => Units::None,
            Some(1) => Units::Kelvin,
            Some(2) => Units::Kelvin,
            Some(3) => Units::Fahrenheit,
            Some(4) => Units::Fahrenheit,
            Some(n) => panic!("invalid size {n} for a nibble"),
        }
    }

    /// The current, one of [Units::Ampere].
    pub fn current(&self) -> Units {
        match self.nibbles().get(3) {
            None | Some(0) => Units::None,
            Some(1..=4) => Units::Ampere,
            Some(n) => panic!("invalid size {n} for a nibble"),
        }
    }

    /// The current, one of [Units::Candela].
    /// Returns [Units::None] if unset.
    pub fn luminosity(&self) -> Units {
        match self.nibbles().get(3) {
            None | Some(0) => Units::None,
            Some(1..=4) => Units::Candela,
            Some(n) => panic!("invalid size {n} for a nibble"),
        }
    }
}

#[derive(Debug, Clone, Copy)]
pub struct UnitExponent(pub u32);

impl UnitExponent {
    fn exponent(&self) -> i8 {
        match self.0 & 0xf {
            n @ 0..=7 => n as i8,
            n @ 8..=15 => -16 + n as i8,
            n => panic!("invalid size {n} for a nibble"),
        }
    }
}

impl_from!(UnitExponent, UnitExponent, u32);
impl_fmt!(UnitExponent, u32);

#[derive(Debug, Clone, Copy)]
pub struct ReportSize(pub usize);

impl_from!(ReportSize, ReportSize, usize);
impl_fmt!(ReportSize, usize);

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct ReportId(pub u8);

impl From<&ReportId> for ReportId {
    fn from(report_id: &ReportId) -> ReportId {
        ReportId(u8::from(report_id))
    }
}

impl_from!(ReportId, ReportId, u8);
impl_fmt!(ReportId, u8);

#[derive(Debug, Clone, Copy)]
pub struct ReportCount(pub usize);

impl_from!(ReportCount, ReportCount, usize);
impl_fmt!(ReportCount, usize);

// ----------------- LOCAL ITEMS --------------------

#[derive(Debug, Clone, Copy)]
pub struct UsageId(pub u16);

impl_from!(UsageId, UsageId, u16);
impl_fmt!(UsageId, u16);

#[derive(Debug, Clone, Copy)]
pub struct UsageMinimum(pub u32);

impl_from!(UsageMinimum, UsageMinimum, u32);
impl_fmt!(UsageMinimum, u32);

#[derive(Debug, Clone, Copy)]
pub struct UsageMaximum(pub u32);

impl_from!(UsageMaximum, UsageMaximum, u32);
impl_fmt!(UsageMaximum, u32);

#[derive(Debug, Clone, Copy)]
pub struct StringIndex(pub u32);

impl_from!(StringIndex, StringIndex, u32);
impl_fmt!(StringIndex, u32);

#[derive(Debug, Clone, Copy)]
pub struct StringMinimum(pub u32);

impl_from!(StringMinimum, StringMinimum, u32);
impl_fmt!(StringMinimum, u32);

#[derive(Debug, Clone, Copy)]
pub struct StringMaximum(pub u32);

impl_from!(StringMaximum, StringMaximum, u32);
impl_fmt!(StringMaximum, u32);

#[derive(Debug, Clone, Copy)]
pub struct DesignatorIndex(pub u32);

impl_from!(DesignatorIndex, DesignatorIndex, u32);
impl_fmt!(DesignatorIndex, u32);

#[derive(Debug, Clone, Copy)]
pub struct DesignatorMinimum(pub u32);

impl_from!(DesignatorMinimum, DesignatorMinimum, u32);
impl_fmt!(DesignatorMinimum, u32);

#[derive(Debug, Clone, Copy)]
pub struct DesignatorMaximum(pub u32);

impl_from!(DesignatorMaximum, DesignatorMaximum, u32);
impl_fmt!(DesignatorMaximum, u32);

#[derive(Debug, Clone, Copy)]
pub struct Delimiter(pub u32);

impl_from!(Delimiter, Delimiter, u32);
impl_fmt!(Delimiter, u32);
