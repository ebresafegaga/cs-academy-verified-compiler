import VectorVerifiedCompiler.Source

namespace VectorVerifiedCompiler

/-- Denotation of a binary operator as a function on integers. -/
def BinOp.denote : BinOp → Int → Int → Int
  | .add => (· + ·)
  | .sub => (· - ·)
  | .mul => (· * ·)

/-- Apply a binary operator to two values. Values are vectors of
integers; a one-element vector is a scalar. Equal lengths combine
elementwise; a scalar broadcasts over the other side; anything else
is a shape error.

Both the interpreter and the stack machine use this same function,
so broadcasting means exactly the same thing in both. -/
def BinOp.apply (op : BinOp) : List Int → List Int → Option (List Int)
  | [x], ys => some (ys.map (op.denote x ·))
  | xs, [y] => some (xs.map (op.denote · y))
  | xs, ys =>
    if xs.length = ys.length then
      some (List.zipWith op.denote xs ys)
    else
      none

/-- The semantics of the source language: an interpreter mapping each
expression to the vector it denotes, or `none` on a shape error. -/
def Expr.eval : Expr → Option (List Int)
  | .const n => some [n]
  | .vconst l => some l
  | .binop op e₁ e₂ => do op.apply (← e₁.eval) (← e₂.eval)

end VectorVerifiedCompiler
