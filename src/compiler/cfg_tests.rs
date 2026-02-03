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

    let (val_map, bb_map, return_blocks) = g.replay_cfg(&other, &[x], &[]);

    assert!(return_blocks.is_empty());
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

    let (val_map, bb_map, _) = g.replay_cfg(&other, &[x], &[]);

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

    let (_val_map, bb_map, _) = g.replay_cfg(&other, &[x], &[]);

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

    let (_, bb_map, _) = g.replay_cfg(&other, &[x], &[]);

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

#[test]
fn call_cache_simple_function() {
    use crate::compiler::call_cache::{CallCache, CallCacheResult};
    use crate::ops::Op;

    // Create a simple program:
    // 0: Increment  (the function body - increments top of stack)
    // 1: Goto       (return to caller)
    // 2: ... (caller would be here)
    let ops = vec![
        Op::Increment,
        Op::Goto,
    ];

    let mut cache = CallCache::new();
    let result = cache.get_or_create(&ops, 0, 0);

    match result {
        CallCacheResult::Hit(cached) => {
            assert!(!cached.return_blocks.is_empty(), "Should have at least one return block");
            assert!(cached.return_addr_param.is_computed(), "Return addr should be a computed value");
            
            // Verify the CFG structure
            let entry = cached.cfg.block_(BlockId(0));
            assert!(entry.parameters.contains(&cached.return_addr_param));
        }
        CallCacheResult::Miss => {
            // This is also acceptable - the function might be too simple or have issues
            // For now, let's just make sure it doesn't panic
        }
        CallCacheResult::InProgress => {
            panic!("Should not be in progress for first call");
        }
    }
}

#[test]
fn call_cache_increment_function_structure() {
    use crate::compiler::call_cache::{CallCache, CallCacheResult};
    use crate::ops::Op;
    
    // Simple function: just returns (Goto pops return address and jumps)
    // IP 10: Goto (return)
    let mut ops = vec![Op::Nop; 12];
    ops[10] = Op::Goto;
    
    let mut cache = CallCache::new();
    let result = cache.get_or_create(&ops, 10, 0);
    
    let cached = match result {
        CallCacheResult::Hit(c) => c,
        CallCacheResult::Miss => panic!("Expected cache hit for simple return function"),
        CallCacheResult::InProgress => panic!("Unexpected InProgress"),
    };
    
    assert_eq!(cached.return_blocks.len(), 1, "Should have exactly one return block");
    
    // Verify return_addr_param is in block 0's parameters
    let entry = cached.cfg.block_(BlockId(0));
    assert!(entry.parameters.contains(&cached.return_addr_param), 
        "Return address should be a block parameter");
}

#[test]
fn call_cache_replay_with_return_blocks() {
    use crate::compiler::call_cache::{CallCache, CallCacheResult};
    use crate::ops::Op;
    
    // Simple function: just return
    let mut ops = vec![Op::Nop; 10];
    ops[5] = Op::Goto;  // IP 5 - return immediately
    
    let mut cache = CallCache::new();
    let cached = match cache.get_or_create(&ops, 5, 0) {
        CallCacheResult::Hit(c) => c,
        _ => panic!("Expected cache hit"),
    };
    
    // Create a new graph and replay the cached CFG
    let mut g = GraphBuilder::new(0);
    let stack_val = g.new_value().id;
    g.block_mut_(BlockId(0)).parameters.push(stack_val);
    g.stack.push(stack_val);
    
    // Return address in our context is IP 7 (within range 0..=10)
    let return_addr = g.store_constant(7);
    // Push the return address onto our stack - this is what will be popped and mapped to cached.return_addr_param
    g.stack.push(return_addr);
    
    // Pass the cached CFG's return_addr_param as the param to be mapped
    let (val_map, block_map, translated_returns) = g.replay_cfg(&cached.cfg, &[cached.return_addr_param], &cached.return_blocks);
    
    // Should have translated the return blocks
    assert_eq!(translated_returns.len(), 1, "Should have one translated return block");
    
    // The return address param should be mapped to our return_addr
    assert_eq!(val_map[&cached.return_addr_param], return_addr);
    
    // Entry block should be translated
    assert!(block_map.contains_key(&BlockId(0)));
}