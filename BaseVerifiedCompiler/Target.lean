import BaseVerifiedCompiler.Semantics

namespace BaseVerifiedCompiler

/-- Instructions of the stack machine. The machine is purely scalar:
it knows nothing about vectors, which are a source-language
abstraction the compiler must lower away. -/
inductive Instr where
  | push (n : Int)
  | binop (op : BinOp)
  deriving Repr, DecidableEq

/-- The machine's operand stack. -/
abbrev Stack := List Int

/-- Run a program against a stack. `push n` pushes `n`; `binop op`
pops the two topmost scalars — right operand on top — and pushes the
result. Scalar operations are total, so the only failure is stack
underflow. -/
def exec : List Instr → Stack → Option Stack
  | [], stk => some stk
  | .push n :: p, stk => exec p (n :: stk)
  | .binop op :: p, y :: x :: stk => exec p (op.denote x y :: stk)
  | .binop _ :: _, _ => none

end BaseVerifiedCompiler
