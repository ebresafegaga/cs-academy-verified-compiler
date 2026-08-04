namespace VerifiedCompiler

/-- Binary operators of the source language. -/
inductive BinOp where
  | add
  | sub
  | mul
  deriving Repr, DecidableEq

/-- Abstract syntax of source expressions: integer constants and
binary operations. -/
inductive Expr where
  | const (n : Int)
  | binop (op : BinOp) (e₁ e₂ : Expr)
  deriving Repr, DecidableEq

end VerifiedCompiler
