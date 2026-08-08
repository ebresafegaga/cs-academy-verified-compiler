import MatrixVerifiedCompiler.Semantics

namespace MatrixVerifiedCompiler

/-- A stack cell: a number, or one of two delimiters. Two dimensions
need two delimiters: with a single mark, a matrix's closing mark
would be indistinguishable from an empty row, and a scalar from a row
fragment. `rowMark` closes a row, `endMark` closes a whole matrix. -/
inductive Cell where
  | val (n : Int)
  | rowMark
  | endMark
  deriving Repr, DecidableEq

/-- The machine's operand stack. A matrix occupies one segment in
row-major order: reading from the top, row `0`'s elements (element
`0` on top) then its `rowMark`, then row `1` likewise, …, and finally
the matrix's `endMark`. -/
abbrev Stack := List Cell

/-- Lay the rows of `m` on top of `s`, each row closed by its
`rowMark` — the segment of `m` except for the closing `endMark`,
which is expected to sit in `s` already. Written
continuation-style (onto `s`, rather than as a standalone list) so
that stack reasoning never fights `++`-associativity. -/
def Mat.rowsOnto : Mat → Stack → Stack
  | [], s => s
  | r :: m, s => r.map .val ++ .rowMark :: Mat.rowsOnto m s

/-- Instructions of the stack machine: push a number, push either
delimiter, or apply an operator to the two topmost matrix segments.
The machine knows nothing about the source language beyond this
segment discipline. -/
inductive Instr where
  | push (n : Int)
  | rowMark
  | endMark
  | binop (op : BinOp)
  deriving Repr, DecidableEq

/-- Pop one matrix segment: parse rows cell by cell until the
matrix's `endMark`. A `rowMark` closes a row; a number joins the row
being read, which must exist — a number directly on an `endMark` is
malformed. Fails on stacks that do not start with a well-formed
segment. -/
def popMat : Stack → Option (Mat × Stack)
  | [] => none
  | .endMark :: s => some ([], s)
  | .rowMark :: s => do
      let (m, s') ← popMat s
      some ([] :: m, s')
  | .val n :: s => do
      let (m, s') ← popMat s
      match m with
      | [] => none
      | r :: m' => some ((n :: r) :: m', s')

/-- Run a program against a stack. `binop op` pops the two topmost
matrix segments — right operand on top — applies the operator (with
the same broadcasting rules as the source semantics, via the shared
`BinOp.apply`), and pushes the delimited result. -/
def exec : List Instr → Stack → Option Stack
  | [], s => some s
  | .push n :: p, s => exec p (.val n :: s)
  | .rowMark :: p, s => exec p (.rowMark :: s)
  | .endMark :: p, s => exec p (.endMark :: s)
  | .binop op :: p, s => do
      let (B, s₁) ← popMat s
      let (A, s₂) ← popMat s₁
      let C ← op.apply A B
      exec p (Mat.rowsOnto C (.endMark :: s₂))

end MatrixVerifiedCompiler
