import ConditionalVerifiedCompiler.Semantics

namespace ConditionalVerifiedCompiler

/-- Instructions of the stack machine. The machine is scalar and
knows nothing about structured control flow: conditionals are a
source-language abstraction the compiler lowers to jumps. Jumps are
relative and forward-only: `jmp k` skips the next `k` instructions;
`jz k` pops the top of the stack and skips the next `k` instructions
if it is zero, otherwise falls through. -/
inductive Instr where
  | push (n : Int)
  | binop (op : BinOp)
  | jmp (k : Nat)
  | jz (k : Nat)
  deriving Repr, DecidableEq

/-- The machine's operand stack. -/
abbrev Stack := List Int

/-- Run a program against a stack. Fails on stack underflow. Because
jumps discard instructions with `List.drop`, this recursion is not
structural; it terminates because every step continues with a strict
suffix of the program, so the program length shrinks. -/
def exec : List Instr → Stack → Option Stack
  | [], stk => some stk
  | .push n :: p, stk => exec p (n :: stk)
  | .binop op :: p, y :: x :: stk => exec p (op.denote x y :: stk)
  | .binop _ :: _, _ => none
  | .jmp k :: p, stk => exec (p.drop k) stk
  | .jz k :: p, c :: stk =>
      if c = 0 then exec (p.drop k) stk else exec p stk
  | .jz _ :: _, [] => none
termination_by p _ => p.length
decreasing_by all_goals simp [List.length_drop] <;> omega

end ConditionalVerifiedCompiler
