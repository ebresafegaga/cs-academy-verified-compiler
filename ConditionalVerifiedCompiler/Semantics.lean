import ConditionalVerifiedCompiler.Source

namespace ConditionalVerifiedCompiler

/-- Denotation of a binary operator as a function on integers. -/
def BinOp.denote : BinOp → Int → Int → Int
  | .add => (· + ·)
  | .sub => (· - ·)
  | .mul => (· * ·)

/-- The semantics of the source language: an interpreter mapping each
expression to the integer it denotes. A conditional takes its `then`
branch exactly when the condition is nonzero. -/
def Expr.eval : Expr → Int
  | .const n => n
  | .binop op e₁ e₂ => op.denote e₁.eval e₂.eval
  | .ite c e₁ e₂ => if c.eval = 0 then e₂.eval else e₁.eval

end ConditionalVerifiedCompiler
