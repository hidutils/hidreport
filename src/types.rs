// SPDX-License-Identifier: MIT

//! A collection of standalone HID types that exist for type safety only.
//! These are all simple wrappers around their underlying integer data type.
//!
//! In this document and unless stated otherwise, a reference to "Section a.b.c" refers to the
//! [HID Device Class Definition for HID 1.11](https://www.usb.org/document-library/device-class-definition-hid-111).

use crate::TwosComplement;
#[cfg(feature = "hut")]
use hut::{self, AsUsage, AsUsagePage};

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
/// The 16-bit Usage Page identifier, see Section 5.5 "Usages".
///
/// The UsagePage forms the upper 16 bits of a 32-bit [Usage](crate::Usage).
/// ```
/// # use hidreport::*;
/// let up = UsagePage::from(0x01); // Generic Desktop
/// let uid = UsageId::from(0x02); // Mouse
/// let usage = Usage::from_page_and_id(up, uid);
/// ```
/// For known named usages see the `hut` crate.
#[derive(Debug, Clone, Copy, PartialEq, PartialOrd)]
pub struct UsagePage(pub(crate) u16);

impl_from!(UsagePage, UsagePage, u16);
impl_fmt!(UsagePage, u16);

#[cfg(feature = "hut")]
impl From<&hut::UsagePage> for UsagePage {
    fn from(hut: &hut::UsagePage) -> UsagePage {
        UsagePage(hut.usage_page_value())
    }
}

#[cfg(feature = "hut")]
impl From<hut::UsagePage> for UsagePage {
    fn from(hut: hut::UsagePage) -> UsagePage {
        UsagePage(hut.usage_page_value())
    }
}

#[cfg(feature = "hut")]
impl From<&hut::Usage> for UsagePage {
    fn from(hut: &hut::Usage) -> UsagePage {
        UsagePage(hut.usage_page_value())
    }
}

#[cfg(feature = "hut")]
impl From<hut::Usage> for UsagePage {
    fn from(hut: hut::Usage) -> UsagePage {
        UsagePage::from(&hut)
    }
}

#[derive(Debug, Clone, Copy, PartialEq, PartialOrd)]
pub struct LogicalMinimum(pub(crate) i32);

impl_from!(LogicalMinimum, LogicalMinimum, i32);
impl_fmt!(LogicalMinimum, i32);

#[derive(Debug, Clone, Copy, PartialEq, PartialOrd)]
pub struct LogicalMaximum(pub(crate) i32);

impl_from!(LogicalMaximum, LogicalMaximum, i32);
impl_fmt!(LogicalMaximum, i32);

#[derive(Debug, Clone, Copy, PartialEq, PartialOrd)]
pub struct PhysicalMinimum(pub(crate) i32);

impl_from!(PhysicalMinimum, PhysicalMinimum, i32);
impl_fmt!(PhysicalMinimum, i32);

#[derive(Debug, Clone, Copy, PartialEq, PartialOrd)]
pub struct PhysicalMaximum(pub(crate) i32);

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

impl From<UnitSystem> for u32 {
    fn from(system: UnitSystem) -> u32 {
        match system {
            UnitSystem::None => 0,
            UnitSystem::SILinear => 1,
            UnitSystem::SIRotation => 2,
            UnitSystem::EnglishLinear => 3,
            UnitSystem::EnglishRotation => 4,
        }
    }
}

#[derive(Debug, Clone, Copy, PartialEq)]
pub enum Units {
    None,
    Centimeter { exponent: i8 },
    Radians { exponent: i8 },
    Inch { exponent: i8 },
    Degrees { exponent: i8 },
    Gram { exponent: i8 },
    Slug { exponent: i8 },
    Seconds { exponent: i8 },
    Kelvin { exponent: i8 },
    Fahrenheit { exponent: i8 },
    Ampere { exponent: i8 },
    Candela { exponent: i8 },
}

impl std::fmt::Display for Units {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let (unit, exp) = match self {
            Units::None => ("", &0i8),
            Units::Centimeter { exponent } => ("cm", exponent),
            Units::Radians { exponent } => ("rad", exponent),
            Units::Inch { exponent } => ("in", exponent),
            Units::Degrees { exponent } => ("deg", exponent),
            Units::Gram { exponent } => ("g", exponent),
            Units::Slug { exponent } => ("slug", exponent),
            Units::Seconds { exponent } => ("s", exponent),
            Units::Kelvin { exponent } => ("K", exponent),
            Units::Fahrenheit { exponent } => ("F", exponent),
            Units::Ampere { exponent } => ("A", exponent),
            Units::Candela { exponent } => ("cd", exponent),
        };

        // quietly clamp to 4 bit range
        let (unit, exp) = match exp {
            0 => ("", 0),
            exp @ -8..=7 => (unit, *exp),
            _ => ("", 0),
        };

        // Superscripts: 0 is skipped altogether and 1 is left out for superscripts
        const SUP: [&str; 16] = [
            "⁻⁸", "⁻⁷", "⁻⁶", "⁻⁵", "⁻⁴", "⁻³", "⁻²", "⁻¹", "", "", "²", "³", "⁴", "⁵", "⁶", "⁷",
        ];
        let exp = SUP[(exp + 8) as usize];
        write!(f, "{unit}{exp}")
    }
}

impl From<Units> for u32 {
    /// Convert from a unit into the byte representation of that unit.
    /// The [UnitSystem] is set only for [Units::Centimeter], [Units::Radians],
    /// [Units::Inch] and [Units::Degrees] where it is non-ambiguous,
    /// for all other values the system is [UnitSystem::None] and needs to
    /// be manually added by the caller:
    ///
    /// ```
    /// # use hidreport::types::*;
    /// let v = u32::from(Units::Centimeter { exponent: -2 });
    /// let unit = Unit::from(v);
    /// assert!(matches!(unit.length(), Units::Centimeter { exponent: -2 }));
    /// // Centimeters are non-ambiguous
    /// assert!(matches!(unit.system(), UnitSystem::SILinear));
    ///
    /// let v = u32::from(Units::Seconds { exponent: 3 });
    /// let unit = Unit::from(v);
    /// assert!(matches!(unit.time(), Units::Seconds { exponent: 3 }));
    /// // Seconds are ambiguous
    /// assert!(matches!(unit.system(), UnitSystem::None));
    ///
    /// // Explicitly set a system
    /// let v = u32::from(UnitSystem::SILinear) | v;
    /// let unit = Unit::from(v);
    /// assert!(matches!(unit.time(), Units::Seconds { exponent: 3 }));
    /// assert!(matches!(unit.system(), UnitSystem::SILinear));
    /// ```
    ///
    /// Any exponent outside the 4-bit twos complement range is quietly ignored
    /// and set to zero.
    fn from(u: Units) -> u32 {
        let (system, nibble, exponent) = match u {
            Units::None => (UnitSystem::None, 0, 0),
            Units::Centimeter { exponent } => (UnitSystem::SILinear, 1, exponent),
            Units::Radians { exponent } => (UnitSystem::SIRotation, 1, exponent),
            Units::Inch { exponent } => (UnitSystem::EnglishLinear, 1, exponent),
            Units::Degrees { exponent } => (UnitSystem::EnglishRotation, 1, exponent),
            Units::Gram { exponent } => (UnitSystem::None, 2, exponent),
            Units::Slug { exponent } => (UnitSystem::None, 2, exponent),
            Units::Seconds { exponent } => (UnitSystem::None, 3, exponent),
            Units::Kelvin { exponent } => (UnitSystem::None, 4, exponent),
            Units::Fahrenheit { exponent } => (UnitSystem::None, 4, exponent),
            Units::Ampere { exponent } => (UnitSystem::None, 5, exponent),
            Units::Candela { exponent } => (UnitSystem::None, 6, exponent),
        };

        let exp: u32 = match exponent {
            exp @ 0..=7 => exp as u32,
            exp @ -8..=-1 => (16 + exp) as u32,
            _ => 0u32,
        };

        u32::from(system) | (exp << (nibble * 4))
    }
}

#[derive(Debug, Clone, Copy, PartialEq)]
pub struct Unit(pub(crate) u32);

impl_from!(Unit, Unit, u32);

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
            Some(n) => panic!("invalid size {n} for the UnitSystem nibble"),
        }
    }

    /// The length, one of [Units::Centimeter], [Units::Radians], [Units::Inch]
    /// or [Units::Degrees] depending on the [UnitSystem].
    /// Returns [Units::None] if unset.
    pub fn length(&self) -> Units {
        match self.nibbles().get(1) {
            None | Some(0) => Units::None,
            Some(n) => {
                let exponent = n.twos_comp(4);
                match self.system() {
                    UnitSystem::None => Units::None,
                    UnitSystem::SILinear => Units::Centimeter { exponent },
                    UnitSystem::SIRotation => Units::Radians { exponent },
                    UnitSystem::EnglishLinear => Units::Inch { exponent },
                    UnitSystem::EnglishRotation => Units::Degrees { exponent },
                }
            }
        }
    }

    /// The mass, one of [Units::Gram] or [Units::Slug] depending
    /// on the [UnitSystem].
    /// Returns [Units::None] if unset.
    pub fn mass(&self) -> Units {
        match self.nibbles().get(2) {
            None | Some(0) => Units::None,
            Some(n) => {
                let exponent = n.twos_comp(4);
                match self.system() {
                    UnitSystem::None => Units::None,
                    UnitSystem::SILinear => Units::Gram { exponent },
                    UnitSystem::SIRotation => Units::Gram { exponent },
                    UnitSystem::EnglishLinear => Units::Slug { exponent },
                    UnitSystem::EnglishRotation => Units::Slug { exponent },
                }
            }
        }
    }

    /// The time, one of [Units::Seconds].
    /// Returns [Units::None] if unset.
    ///
    /// This unit is not [UnitSystem] dependent and will return
    /// the right value regardless of the [UnitSystem] set.
    pub fn time(&self) -> Units {
        match self.nibbles().get(3) {
            None | Some(0) => Units::None,
            Some(n) => {
                let exponent = n.twos_comp(4);
                Units::Seconds { exponent }
            }
        }
    }

    /// The time, one of [Units::Kelvin] or [Units::Fahrenheit],
    /// depending on the [UnitSystem].
    /// Returns [Units::None] if unset.
    ///
    /// This unit is not [UnitSystem] dependent and will return
    /// the right value regardless of the [UnitSystem] set.
    pub fn temperature(&self) -> Units {
        match self.nibbles().get(4) {
            None | Some(0) => Units::None,
            Some(n) => {
                let exponent = n.twos_comp(4);
                match self.system() {
                    UnitSystem::None => Units::None,
                    UnitSystem::SILinear => Units::Kelvin { exponent },
                    UnitSystem::SIRotation => Units::Kelvin { exponent },
                    UnitSystem::EnglishLinear => Units::Fahrenheit { exponent },
                    UnitSystem::EnglishRotation => Units::Fahrenheit { exponent },
                }
            }
        }
    }

    /// The current, one of [Units::Ampere].
    ///
    /// This unit is not [UnitSystem] dependent and will return
    /// the right value regardless of the [UnitSystem] set.
    pub fn current(&self) -> Units {
        match self.nibbles().get(5) {
            None | Some(0) => Units::None,
            Some(n) => {
                let exponent = n.twos_comp(4);
                Units::Ampere { exponent }
            }
        }
    }

    /// The current, one of [Units::Candela].
    /// Returns [Units::None] if unset.
    ///
    /// This unit is not [UnitSystem] dependent and will return
    /// the right value regardless of the [UnitSystem] set.
    pub fn luminosity(&self) -> Units {
        match self.nibbles().get(6) {
            None | Some(0) => Units::None,
            Some(n) => {
                let exponent = n.twos_comp(4);
                Units::Candela { exponent }
            }
        }
    }
}

impl std::fmt::Display for Unit {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let units = self
            .units()
            .unwrap_or_default()
            .iter()
            .map(|u| format!("{u}"))
            .collect::<Vec<String>>()
            .join("");
        write!(f, "{units}")
    }
}

#[derive(Debug, Clone, Copy, PartialEq)]
pub struct UnitExponent(pub(crate) i32);

impl UnitExponent {
    pub fn exponent(&self) -> i8 {
        // Section 6.2.2.7 lists an example implying that
        // the unit exponent must be a nibble. Real devices
        // can send either a nibble or a normal value, let's
        // handle either.
        match self.0 {
            // nibble
            n @ 0..=7 => n as i8,
            n @ 8..=15 => -16 + n as i8,
            // normal value
            n => n as i8,
        }
    }
}

impl_from!(UnitExponent, UnitExponent, i32);
impl_fmt!(UnitExponent, i32);

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct ReportSize(pub(crate) usize);

impl_from!(ReportSize, ReportSize, usize);
impl_fmt!(ReportSize, usize);

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct ReportId(pub(crate) u8);

impl From<&ReportId> for ReportId {
    fn from(report_id: &ReportId) -> ReportId {
        ReportId(u8::from(report_id))
    }
}

impl_from!(ReportId, ReportId, u8);
impl_fmt!(ReportId, u8);

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct ReportCount(pub(crate) usize);

impl_from!(ReportCount, ReportCount, usize);
impl_fmt!(ReportCount, usize);

// ----------------- LOCAL ITEMS --------------------

/// The 16-bit Usage Id identifier, see Section 5.5 "Usages".
///
/// The UsageId forms the lower 16 bits of a 32-bit [Usage](crate::Usage).
/// ```
/// # use hidreport::*;
/// let up = UsagePage::from(0x01); // Generic Desktop
/// let uid = UsageId::from(0x02); // Mouse
/// let usage = Usage::from_page_and_id(up, uid);
/// ```
/// For known named usages see the `hut` crate.
#[derive(Debug, Clone, Copy, PartialEq, PartialOrd)]
pub struct UsageId(pub(crate) u16);

impl_from!(UsageId, UsageId, u16);
impl_fmt!(UsageId, u16);

#[cfg(feature = "hut")]
impl From<&hut::Usage> for UsageId {
    fn from(hut: &hut::Usage) -> UsageId {
        UsageId(hut.usage_id_value())
    }
}

#[cfg(feature = "hut")]
impl From<hut::Usage> for UsageId {
    fn from(hut: hut::Usage) -> UsageId {
        UsageId::from(&hut)
    }
}

#[derive(Debug, Clone, Copy, PartialEq, PartialOrd)]
pub struct UsageMinimum(pub(crate) u32);

impl UsageMinimum {
    pub fn usage_id(&self) -> UsageId {
        UsageId::from((self.0 & 0xffff) as u16)
    }

    pub fn usage_page(&self) -> UsagePage {
        UsagePage((self.0 >> 16) as u16)
    }
}

impl_from!(UsageMinimum, UsageMinimum, u32);
impl_fmt!(UsageMinimum, u32);

#[derive(Debug, Clone, Copy, PartialEq, PartialOrd)]
pub struct UsageMaximum(pub(crate) u32);

impl UsageMaximum {
    pub fn usage_id(&self) -> UsageId {
        UsageId::from((self.0 & 0xffff) as u16)
    }

    pub fn usage_page(&self) -> UsagePage {
        UsagePage((self.0 >> 16) as u16)
    }
}

impl_from!(UsageMaximum, UsageMaximum, u32);
impl_fmt!(UsageMaximum, u32);

#[derive(Debug, Clone, Copy, PartialEq)]
pub struct StringIndex(pub(crate) u32);

impl_from!(StringIndex, StringIndex, u32);
impl_fmt!(StringIndex, u32);

#[derive(Debug, Clone, Copy, PartialEq)]
pub struct StringMinimum(pub(crate) u32);

impl_from!(StringMinimum, StringMinimum, u32);
impl_fmt!(StringMinimum, u32);

#[derive(Debug, Clone, Copy, PartialEq)]
pub struct StringMaximum(pub(crate) u32);

impl_from!(StringMaximum, StringMaximum, u32);
impl_fmt!(StringMaximum, u32);

#[derive(Debug, Clone, Copy, PartialEq)]
pub struct DesignatorIndex(pub(crate) u32);

impl_from!(DesignatorIndex, DesignatorIndex, u32);
impl_fmt!(DesignatorIndex, u32);

#[derive(Debug, Clone, Copy, PartialEq)]
pub struct DesignatorMinimum(pub(crate) u32);

impl_from!(DesignatorMinimum, DesignatorMinimum, u32);
impl_fmt!(DesignatorMinimum, u32);

#[derive(Debug, Clone, Copy, PartialEq)]
pub struct DesignatorMaximum(pub(crate) u32);

impl_from!(DesignatorMaximum, DesignatorMaximum, u32);
impl_fmt!(DesignatorMaximum, u32);

#[derive(Debug, Clone, Copy, PartialEq)]
pub struct Delimiter(pub(crate) u32);

impl_from!(Delimiter, Delimiter, u32);
impl_fmt!(Delimiter, u32);

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_units() {
        for nibble in 1..=6 {
            // SILinear and SIRotation
            for system in 1..=2 {
                let exp = 2;
                let v = system | exp << (4 * nibble);
                let u = Unit::from(v);
                match system {
                    1 => assert!(matches!(u.system(), UnitSystem::SILinear)),
                    2 => assert!(matches!(u.system(), UnitSystem::SIRotation)),
                    _ => panic!("Invalid system value"),
                };
                match nibble {
                    1 => match system {
                        0x1 => assert!(matches!(u.length(), Units::Centimeter { exponent: 2 })),
                        0x2 => assert!(matches!(u.length(), Units::Radians { exponent: 2 })),
                        _ => panic!("Invalid system value"),
                    },
                    2 => assert!(matches!(u.mass(), Units::Gram { exponent: 2 })),
                    3 => assert!(matches!(u.time(), Units::Seconds { exponent: 2 })),
                    4 => assert!(matches!(u.temperature(), Units::Kelvin { exponent: 2 })),
                    5 => assert!(matches!(u.current(), Units::Ampere { exponent: 2 })),
                    6 => assert!(matches!(u.luminosity(), Units::Candela { exponent: 2 })),
                    _ => panic!("Invalid nibble value"),
                }
            }

            // EnglishLinear and EnglishRotation
            for system in 3..=4 {
                let exp = 0xd; // two's comp for -3
                let v = system | exp << (4 * nibble);
                let u = Unit::from(v);
                match system {
                    3 => assert!(matches!(u.system(), UnitSystem::EnglishLinear)),
                    4 => assert!(matches!(u.system(), UnitSystem::EnglishRotation)),
                    _ => panic!("Invalid system value"),
                };
                match nibble {
                    1 => match system {
                        0x3 => assert!(matches!(u.length(), Units::Inch { exponent: -3 })),
                        0x4 => assert!(matches!(u.length(), Units::Degrees { exponent: -3 })),
                        _ => panic!("Invalid system value"),
                    },
                    2 => assert!(matches!(u.mass(), Units::Slug { exponent: -3 })),
                    3 => assert!(matches!(u.time(), Units::Seconds { exponent: -3 })),
                    4 => assert!(matches!(
                        u.temperature(),
                        Units::Fahrenheit { exponent: -3 }
                    )),
                    5 => assert!(matches!(u.current(), Units::Ampere { exponent: -3 })),
                    6 => assert!(matches!(u.luminosity(), Units::Candela { exponent: -3 })),
                    _ => panic!("Invalid nibble value"),
                }
            }
        }

        // The various examples from Section 6.2.2.7, page 39
        // Energy
        let u = Unit::from(0xE121);
        assert!(matches!(u.system(), UnitSystem::SILinear));
        assert!(matches!(u.length(), Units::Centimeter { exponent: 2 }));
        assert!(matches!(u.mass(), Units::Gram { exponent: 1 }));
        assert!(matches!(u.time(), Units::Seconds { exponent: -2 }));
        assert!(matches!(u.current(), Units::None));
        assert!(matches!(u.luminosity(), Units::None));
        assert!(matches!(u.temperature(), Units::None));
        assert_eq!(format!("{u}"), "cm²gs⁻²");

        // Angular Acceleration
        let u = Unit::from(0xE012);
        assert!(matches!(u.system(), UnitSystem::SIRotation));
        assert!(matches!(u.length(), Units::Radians { exponent: 1 }));
        assert!(matches!(u.mass(), Units::None));
        assert!(matches!(u.time(), Units::Seconds { exponent: -2 }));
        assert!(matches!(u.current(), Units::None));
        assert!(matches!(u.temperature(), Units::None));
        assert!(matches!(u.luminosity(), Units::None));
        assert_eq!(format!("{u}"), "rads⁻²");

        // Voltage
        let u = Unit::from(0x00F0D121);
        assert!(matches!(u.system(), UnitSystem::SILinear));
        assert!(matches!(u.length(), Units::Centimeter { exponent: 2 }));
        assert!(matches!(u.mass(), Units::Gram { exponent: 1 }));
        assert!(matches!(u.time(), Units::Seconds { exponent: -3 }));
        assert!(matches!(u.current(), Units::Ampere { exponent: -1 }));
        assert!(matches!(u.temperature(), Units::None));
        assert!(matches!(u.luminosity(), Units::None));
        assert_eq!(format!("{u}"), "cm²gs⁻³A⁻¹");
    }

    #[test]
    fn test_unit_conversion() {
        for exp in 1..=15 {
            for nibble in 1..=6 {
                let v = 0x1u32 | (exp << (nibble * 4)); // SILinear
                let unit = Unit::from(v);
                assert_eq!(u32::from(unit), v);

                // Compose the values from the units() vector
                let uval = u32::from(unit.system())
                    | unit
                        .units()
                        .unwrap()
                        .iter()
                        .fold(0, |acc, u| acc | u32::from(*u));
                assert_eq!(uval, v);
            }
        }
    }

    #[test]
    fn unit_exponent() {
        let testvals = vec![
            (0xf, -1),  // nibble test
            (0xe, -2),  // nibble test
            (0x8, -8),  // nibble test
            (0x7, 7),   // normal or nibble
            (0x1, 1),   // normal or nibble
            (0xff, -1), // normal value
            (0xfd, -3), // normal value
            (0x10, 16), // normal value
        ];

        for (v, expected) in testvals {
            let exponent = UnitExponent::from(v);
            assert_eq!(exponent.exponent(), expected);
        }
    }

    #[cfg(feature = "hut")]
    #[test]
    fn hut() {
        let up = UsagePage::from(hut::UsagePage::GenericDesktop);
        assert_eq!(u16::from(up), 0x1);

        let up = UsagePage::from(&hut::UsagePage::GenericDesktop);
        assert_eq!(u16::from(up), 0x1);

        let u = UsagePage::from(hut::GenericDesktop::X.usage());
        assert_eq!(u16::from(u), 0x1);

        let u = UsagePage::from(&hut::GenericDesktop::X.usage());
        assert_eq!(u16::from(u), 0x1);

        let u = UsageId::from(hut::GenericDesktop::X.usage());
        assert_eq!(u16::from(u), 0x30);

        let u = UsageId::from(&hut::GenericDesktop::X.usage());
        assert_eq!(u16::from(u), 0x30);
    }
}
