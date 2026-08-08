import VectorVerifiedCompiler.Semantics

namespace VectorVerifiedCompiler

/-- A stack cell: a number, or the delimiter. The delimiter must be a
distinct kind of cell — on a stack of bare integers every bit pattern
is data, so no integer could serve as a sentinel. -/
inductive Cell where
  | val (n : Int)
  | mark
  deriving Repr, DecidableEq

/-- The machine's operand stack. A value occupies one delimited
segment: its `mark`, with the elements above it and element `0` on
top. A scalar is simply a one-element segment. -/
abbrev Stack := List Cell

/-- Instructions of the stack machine: push a number, push the
delimiter, or apply an operator to the two topmost delimited
segments. The machine knows nothing about the source language's
vectors beyond "a value is the stack down to the next `mark`". -/
inductive Instr where
  | push (n : Int)
  | mark
  | binop (op : BinOp)
  deriving Repr, DecidableEq

/-- Pop one value: collect numbers down to the nearest `mark`, pop
that too. Fails if the delimiter is missing or a `mark` interrupts
nothing — i.e. on stacks that are not sequences of well-formed
values. -/
def popValue : Stack → Option (List Int × Stack)
  | [] => none
  | .mark :: s => some ([], s)
  | .val n :: s => do
      let (l, s') ← popValue s
      some (n :: l, s')

/-- Run a program against a stack. `binop op` pops the two topmost
delimited segments — right operand on top — applies the operator
(with the same broadcasting rules as the source semantics, via the
shared `BinOp.apply`), and pushes the delimited result. -/
def exec : List Instr → Stack → Option Stack
  | [], s => some s
  | .push n :: p, s => exec p (.val n :: s)
  | .mark :: p, s => exec p (.mark :: s)
  | .binop op :: p, s => do
      let (ys, s₁) ← popValue s
      let (xs, s₂) ← popValue s₁
      let zs ← op.apply xs ys
      exec p (zs.map .val ++ .mark :: s₂)

end VectorVerifiedCompiler
