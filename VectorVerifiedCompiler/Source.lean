namespace VectorVerifiedCompiler

/-- Binary operators of the source language. -/
inductive BinOp where
  | add
  | sub
  | mul
  deriving Repr, DecidableEq

/-- Abstract syntax: the base expression language extended with
vector literals. Semantically a scalar *is* a one-element vector
(APL-style); `const n` is just convenient syntax for `vconst [n]`.
This identification is deliberate: values live on the target's stack
as delimiter-bracketed runs of numbers, and a pure run of numbers
cannot distinguish `3` from `[3]` — so the language does not
either. -/
inductive Expr where
  | const (n : Int)
  | vconst (l : List Int)
  | binop (op : BinOp) (e₁ e₂ : Expr)
  deriving Repr, DecidableEq

end VectorVerifiedCompiler
