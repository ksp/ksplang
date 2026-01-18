use crate::compiler::{cfg::GraphBuilder, ops::{BlockId, OptOp, ValueId}, osmibytecode::Condition};


#[test]
fn replay_cfg_straight_line() {
    let mut other = GraphBuilder::new(0);
    let x = other.new_value().id;
    other.block_mut_(BlockId(0)).parameters.push(x);
    let (_y, _) = other.push_instr(OptOp::Add, &[x, ValueId::C_ONE], false, None, None);

    let mut g = GraphBuilder::new(0);
    let gx = g.new_value().id;
    g.block_mut_(BlockId(0)).parameters.push(gx);
    g.stack.push(gx);

    let (val_map, bb_map) = g.replay_cfg(&other, &[x]);

    assert_eq!(bb_map[&BlockId(0)], g.current_block);
    assert_eq!(val_map[&x], gx);

    let entry_block = g.block_(BlockId(0));
    let add = entry_block
        .instructions
        .values()
        .find(|i| matches!(i.op, OptOp::Add))
        .expect("missing Add instruction");
    assert!(add.out.is_computed());
    assert_eq!(add.inputs.len(), 2);
    assert!(add.inputs.contains(&gx));
    assert!(add.inputs.contains(&ValueId::C_ONE));
}

#[test]
fn replay_cfg_branches_create_blocks_and_jumps() {
    // replay_cfg: branches create corresponding blocks and jumps
    let mut other = GraphBuilder::new(0);
    let x = other.new_value().id;
    other.block_mut_(BlockId(0)).parameters.push(x);
    let (y, _) = other.push_instr(OptOp::Add, &[x, ValueId::C_ONE], false, None, None);
    let (z, _) = other.push_instr(OptOp::Add, &[x, ValueId::C_TWO], false, None, None);

    let b1 = other.new_block(0, true, vec![]).id;
    let b2 = other.new_block(0, true, vec![]).id;

    let j1 = other
        .push_instr(OptOp::Jump(Condition::Lt(x, ValueId::C_ZERO), b1), &[y], false, None, None)
        .1
        .unwrap()
        .id;
    let j2 = other
        .push_instr(OptOp::Jump(Condition::True, b2), &[z], false, None, None)
        .1
        .unwrap()
        .id;

    other.block_mut_(b1).incoming_jumps.push(j1);
    other.block_mut_(b1).predecessors.insert(BlockId(0));
    other.block_mut_(b2).incoming_jumps.push(j2);
    other.block_mut_(b2).predecessors.insert(BlockId(0));

    let mut g = GraphBuilder::new(0);
    let gx = g.new_value().id;
    g.block_mut_(BlockId(0)).parameters.push(gx);
    g.stack.push(gx);

    let (val_map, bb_map) = g.replay_cfg(&other, &[x]);

    assert!(bb_map.contains_key(&BlockId(0)));
    assert!(bb_map.contains_key(&b1));
    assert!(bb_map.contains_key(&b2));

    assert_eq!(val_map[&x], gx);
    let gy = val_map[&y];
    let gz = val_map[&z];

    let add_y = g.get_defined_at(gy).unwrap();
    assert!(matches!(add_y.op, OptOp::Add));
    assert_eq!(add_y.inputs.len(), 2);
    assert!(add_y.inputs.contains(&gx));
    assert!(add_y.inputs.contains(&ValueId::C_ONE));

    let add_z = g.get_defined_at(gz).unwrap();
    assert!(matches!(add_z.op, OptOp::Add));
    assert_eq!(add_z.inputs.len(), 2);
    assert!(add_z.inputs.contains(&gx));
    assert!(add_z.inputs.contains(&ValueId::C_TWO));

    let entry_block = g.block_(bb_map[&BlockId(0)]);
    let jumps: Vec<_> = entry_block
        .instructions
        .values()
        .filter(|i| matches!(i.op, OptOp::Jump(..)))
        .collect();
    assert_eq!(jumps.len(), 2);
}

#[test]
fn replay_cfg_handles_loops_without_infinite_recursion() {
    // replay_cfg: loops do not cause infinite traversal
    let mut other = GraphBuilder::new(0);
    let x = other.new_value().id;
    other.block_mut_(BlockId(0)).parameters.push(x);

    let (y, _) = other.push_instr(OptOp::Add, &[x, ValueId::C_ONE], false, None, None);

    let b1 = other.new_block(0, true, vec![]).id;

    let j0 = other
        .push_instr(OptOp::Jump(Condition::True, b1), &[y], false, None, None)
        .1
        .unwrap()
        .id;
    other.block_mut_(b1).incoming_jumps.push(j0);
    other.block_mut_(b1).predecessors.insert(BlockId(0));

    other.switch_to_block(b1, 0, vec![]);

    let (y2, _) = other.push_instr(OptOp::Add, &[y, ValueId::C_ONE], false, None, None);
    let j1 = other
        .push_instr(OptOp::Jump(Condition::True, b1), &[y2], false, None, None)
        .1
        .unwrap()
        .id;
    other.block_mut_(b1).incoming_jumps.push(j1);
    other.block_mut_(b1).predecessors.insert(b1);

    let mut g = GraphBuilder::new(0);
    let gx = g.new_value().id;
    g.block_mut_(BlockId(0)).parameters.push(gx);
    g.stack.push(gx);

    let (_val_map, bb_map) = g.replay_cfg(&other, &[x]);

    assert!(bb_map.contains_key(&BlockId(0)));
    assert!(bb_map.contains_key(&b1));
}

#[test]
fn replay_cfg_complex_constants() {
    // replay_cfg: non-predefined constants are re-created, not re-used by id
    let mut other = GraphBuilder::new(0);
    let c1 = other.store_constant(123456);
    let x = other.new_value().id;
    other.block_mut_(BlockId(0)).parameters.push(x);
    
    other.push_instr(OptOp::Add, &[x, c1], false, None, None);

    let mut g = GraphBuilder::new(0);
    g.store_constant(987654);
    let gx = g.new_value().id;
    g.block_mut_(BlockId(0)).parameters.push(gx);
    g.stack.push(gx);

    let (_, bb_map) = g.replay_cfg(&other, &[x]);

    let entry_block = g.block_(bb_map[&BlockId(0)]);
    let add = entry_block
        .instructions
        .values()
        .find(|i| matches!(i.op, OptOp::Add) && i.inputs.contains(&gx))
        .expect("Did not find replayed instruction");

    let const_operand = *add.inputs.iter().find(|&&v| v != gx).unwrap();
    let val = g.get_constant(const_operand).expect("Operand should be a constant");
    assert_eq!(val, 123456);
}
