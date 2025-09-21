use std::collections::HashMap;

use crate::compiler::{cfg::{InstrId, ValueId}, vm_code::Condition};



struct TraceTree {
    trace: HashMap<ValueId, InstrId>,
    path_constraints: Vec<Condition<ValueId>>,
    branching: Vec<TraceTree>,
}


// /// Returns a list of all instruction traces that could have produced the given value, up to max_len instructions long.
// /// Multiple traces are returned if the value is produced by a phi node (block param), i.e. control flow is involved.
// pub fn trace_value_origin(cfg: Builder, val: ValueId, max_len: usize, max_count: usize) -> Vec<Vec<InstrId>> {
//     let val1 = self.values[&val];
//     let instr = self.get_instruction(val1.assigned_at).unwrap();
//     let wavefront: Vec<()
// }

// /// Returns a list of possible value combinations for the given ValueIds, if the set is small enough.
// pub fn please_please_find_its_a_constant(&self, max_size: usize, vals: &[ValueId]) -> Option<Vec<Vec<i64>>> {
//     let val_infos = vals.iter().map(|v| self.values[v]).collect::<Vec<_>>();
    
// }
