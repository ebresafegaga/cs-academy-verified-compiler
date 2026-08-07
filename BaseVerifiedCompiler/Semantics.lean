import BaseVerifiedCompiler.Source

namespace BaseVerifiedCompiler

/-- Denotation of a binary operator as a function on integers. -/
def BinOp.denote : BinOp → Int → Int → Int
  | .add => (· + ·)
  | .sub => (· - ·)
  | .mul => (· * ·)

/-- The semantics of the source language: an interpreter mapping each
expression to the integer it denotes. -/
def Expr.eval : Expr → Int
  | .const n => n
  | .binop op e₁ e₂ => op.denote e₁.eval e₂.eval

end BaseVerifiedCompiler
