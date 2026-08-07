namespace ConditionalVerifiedCompiler

/-- Binary operators of the source language. -/
inductive BinOp where
  | add
  | sub
  | mul
  deriving Repr, DecidableEq

/-- Abstract syntax of source expressions: integer constants, binary
operations, and conditionals. `ite c e₁ e₂` is if-then-else with
C-style truthiness: it means `e₁` when `c` is nonzero and `e₂` when
`c` is zero. -/
inductive Expr where
  | const (n : Int)
  | binop (op : BinOp) (e₁ e₂ : Expr)
  | ite (c e₁ e₂ : Expr)
  deriving Repr, DecidableEq

end ConditionalVerifiedCompiler
