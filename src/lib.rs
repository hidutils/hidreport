// SPDX-License-Identifier: MIT
//
// FIXME: remove this once we have something that doesn't scream hundreds of warnings
#![allow(unused_variables)]
#![allow(dead_code)]

use std::ops::Range;
use thiserror::Error;

pub mod hid;
pub mod hut;
pub mod types;

use hid::*;
pub use types::*;

#[derive(Debug)]
pub struct ReportDescriptor {
    pub input_reports: Vec<Report>,
    pub output_reports: Vec<Report>,
    pub feature_reports: Vec<Report>,
}

impl ReportDescriptor {}

#[derive(Debug)]
pub enum ReportType {
    Input,
    Output,
    Feature,
}

#[derive(Debug)]
pub struct Report {
    /// The report ID, if any
    pub id: Option<u8>,
    /// The size of this report in bits
    pub size: usize,
    /// The fields present in this report
    pub items: Vec<VariableField>,
    pub report_type: ReportType,
}

#[derive(Debug)]
pub struct Usage {
    usage_page: UsagePage,
    usage_id: UsageId,
}

#[derive(Debug)]
pub struct LogicalRange {
    minimum: LogicalMinimum,
    maximum: LogicalMaximum,
}

#[derive(Debug)]
pub struct PhysicalRange {
    minimum: PhysicalMinimum,
    maximum: PhysicalMaximum,
}

#[derive(Debug)]
pub struct VariableField {
    usage: Option<Usage>,
    bits: Range<u32>,
    logical_range: LogicalRange,
    pyhsical_range: Option<PhysicalRange>,
    unit: Option<Unit>,
    unit_exponent: Option<UnitExponent>,
    collections: Vec<Collection>,
}

#[derive(Debug)]
pub struct ArrayField {
    usage_list: Vec<Usage>,
    bits: Range<u32>,
    logical_range: LogicalRange,
    pyhsical_range: Option<PhysicalRange>,
    unit: Option<Unit>,
    unit_exponent: Option<UnitExponent>,
    collections: Vec<Collection>,
}

#[derive(Debug)]
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

impl TryFrom<&[u8]> for ReportDescriptor {
    type Error = ParserError;

    fn try_from(bytes: &[u8]) -> Result<ReportDescriptor> {
        panic!("fixme");
    }
}

#[derive(Clone, Debug, Default)]
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
#[derive(Clone, Debug)]
struct LocalUsage {
    usage_page: Option<UsagePage>,
    usage_id: UsageId,
}

#[derive(Clone, Debug, Default)]
struct Locals {
    usage: Option<LocalUsage>,
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

#[derive(Clone, Debug, Default)]
struct State {
    pub globals: Globals,
    pub locals: Locals,
}

#[derive(Debug, Default)]
struct Stack {
    states: Vec<State>,
    collections: Vec<Collection>,
}

impl Stack {
    fn new() -> Self {
        Stack {
            states: vec![State::default()],
            collections: vec![],
        }
    }

    fn push(&mut self) {
        let current = &self.states[0];
        self.states.push(current.clone());
    }

    fn pop(&mut self) {
        self.states.pop();
    }

    fn state(&mut self) -> &mut State {
        self.states.last_mut().unwrap()
    }
}

macro_rules! update_stack {
    ($stack:ident, $class:ident, $which:ident, $from:ident) => {
        let state = $stack.state();
        state.$class.$which = Some($from);
    };
}

fn parse_report_descriptor(bytes: &[u8]) -> Result<ReportDescriptor> {
    let items = hid::ReportDescriptorItems::try_from(bytes)?;

    let mut stack = Stack::default();
    stack.push();

    for rdesc_item in items.iter() {
        let item = rdesc_item.item();
        match item.item_type() {
            ItemType::Main(MainItem::Input(i)) => {}
            ItemType::Main(MainItem::Output(o)) => {}
            ItemType::Main(MainItem::Feature(i)) => {}
            ItemType::Main(MainItem::Collection(i)) => {
                let c = Collection(u8::from(&i));
                stack.collections.push(c);
            }
            ItemType::Main(MainItem::EndCollection) => {
                stack.collections.pop(c);
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
                update_stack!(stack, locals, usage, usage);
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
        }
    }

    panic!("fixme");
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn it_works() {}
}
