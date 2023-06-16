use crate::ops::Op;

#[derive(Clone, Debug)]
struct State {
    stack: Vec<i64>,
}

impl State {
    fn new() -> Self {
        State {
            stack: Vec::new(),
        }
    }

    fn clear(&mut self) {
        self.stack.clear();
    }

    fn push(&mut self, value: i64) {
        self.stack.push(value)
    }

    fn len(&self) -> usize {
        self.stack.len()
    }

    fn peek(&self) -> Option<i64> {
        self.stack.last().copied()
    }

    /// Indexed from the bottom of the stack
    fn get(&self, index: usize) -> Option<i64> {
        self.stack.get(index).copied()
    }

    fn apply(&mut self, op: Op) -> Option<()> {
        match op {
            Op::Const0 => self.stack.push(0),
            Op::Const1 => self.stack.push(1),
            Op::Const2 => self.stack.push(2),
            Op::Const3 => self.stack.push(3),
            Op::Const4 => self.stack.push(4),
            Op::Const5 => self.stack.push(5),
            Op::Const6 => self.stack.push(6),
            Op::Const7 => self.stack.push(7),
            Op::Const8 => self.stack.push(8),
            Op::Const9 => self.stack.push(9),
            Op::Add => {
                let a = self.stack.pop()?;
                let b = self.stack.pop()?;
                self.stack.push(a.checked_add(b)?);
            }
            Op::Copy => {
                let offset = self.stack.pop()?;
                let pos = self.stack.len().checked_sub(1usize.checked_add(offset as usize)?)?;
                let value = self.stack.get(pos)?;
                self.stack.push(*value);
            }
            Op::Dup => {
                let a = self.stack.pop()?;
                self.stack.push(a);
                self.stack.push(a);
            }
            Op::Equal => {
                let a = self.stack.pop()?;
                let b = self.stack.pop()?;
                if a == b {
                    self.stack.push(1)
                } else {
                    self.stack.push(0)
                }
            }
            Op::Greater => {
                let b = self.stack.pop()?;
                let a = self.stack.pop()?;
                if a > b {
                    self.stack.push(1)
                } else {
                    self.stack.push(0)
                }
            }
            Op::Count => {
                let length: i64 = i64::try_from(self.stack.len()).ok()?;
                self.stack.push(length)
            }
            Op::Less => {
                let b = self.stack.pop()?;
                let a = self.stack.pop()?;
                if a < b {
                    self.stack.push(1)
                } else {
                    self.stack.push(0)
                }
            }
            Op::Mul => {
                let a = self.stack.pop()?;
                let b = self.stack.pop()?;
                self.stack.push(a.checked_mul(b)?);
            }
            Op::Overwrite => {
                let value = self.stack.pop()?;
                let offset = self.stack.pop()?;
                let pos = self.stack.len().checked_sub(1usize.checked_add(offset as usize)?)?;
                let rewritten = self.stack.get_mut(pos)?;
                *rewritten = value
            }
            Op::Pop => {
                self.stack.pop()?;
            }
            Op::Quotient => {
                let b = self.stack.pop()?;
                let a = self.stack.pop()?;
                self.stack.push(a.checked_div(b)?);
            }
            Op::Remainder => {
                let b = self.stack.pop()?;
                let a = self.stack.pop()?;
                if b < 0 { return None }
                self.stack.push(a.checked_rem(b)?);
            }
            Op::Subtract => {
                let b = self.stack.pop()?;
                let a = self.stack.pop()?;
                self.stack.push(a.checked_sub(b)?);
            }
            Op::Exchange => {
                let a = self.stack.pop()?;
                let b = self.stack.pop()?;
                self.stack.push(a);
                self.stack.push(b);
            }
            Op::Nop => {}
        }

        Some(())
    }
}

pub fn run_with_empty_stack(ops: &[Op]) -> Option<i64> {
    let mut state = State::new();

    for op in ops {
        state.apply(*op)?;
    }

    state.peek()
}

pub fn run_with_stack(ops: &[Op], stack: &[i64]) -> Option<i64> {
    let mut state = State::new();
    for value in stack.iter().rev() {
        state.push(*value);
    }

    for op in ops {
        state.apply(*op)?;
    }

    state.peek()
}
