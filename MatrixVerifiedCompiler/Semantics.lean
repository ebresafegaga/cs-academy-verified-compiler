import MatrixVerifiedCompiler.Source

namespace MatrixVerifiedCompiler

/-- Denotation of a binary operator as a function on integers. -/
def BinOp.denote : BinOp → Int → Int → Int
  | .add => (· + ·)
  | .sub => (· - ·)
  | .mul => (· * ·)

/-- Apply a binary operator to two matrices. A `1 × 1` matrix (a
scalar) broadcasts over the other side; otherwise the row-length
profiles must agree and the operation is elementwise.

Both the interpreter and the stack machine use this same function, so
broadcasting and shape errors mean the same thing in both. -/
def BinOp.apply (op : BinOp) : Mat → Mat → Option Mat
  | [[x]], B => some (B.map (List.map (op.denote x ·)))
  | A, [[y]] => some (A.map (List.map (op.denote · y)))
  | A, B =>
    if A.map List.length = B.map List.length then
      some (List.zipWith (List.zipWith op.denote) A B)
    else
      none

/-- The semantics of the source language: an interpreter mapping each
expression to the matrix it denotes, or `none` on a shape error. -/
def Expr.eval : Expr → Option Mat
  | .const n => some [[n]]
  | .vconst l => some [l]
  | .mconst m => some m
  | .binop op e₁ e₂ => do op.apply (← e₁.eval) (← e₂.eval)

end MatrixVerifiedCompiler
