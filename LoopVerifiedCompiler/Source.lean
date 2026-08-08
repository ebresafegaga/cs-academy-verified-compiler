namespace LoopVerifiedCompiler

/-- Binary operators of the source language. -/
inductive BinOp where
  | add
  | sub
  | mul
  deriving Repr, DecidableEq

/-- Expressions: integer constants, variables, and binary operations.
Expressions are pure — they read the state but never change it. -/
inductive Expr where
  | const (n : Int)
  | var (x : String)
  | binop (op : BinOp) (e₁ e₂ : Expr)
  deriving Repr, DecidableEq

/-- Statements. `whileDo c body` is the delta of this extension:
it repeats `body` as long as `c` is nonzero (C-style truthiness).
Loops are only meaningful with mutable state, so the language also
has assignment and sequencing. -/
inductive Stmt where
  | skip
  | assign (x : String) (e : Expr)
  | seq (s₁ s₂ : Stmt)
  | whileDo (c : Expr) (body : Stmt)
  deriving Repr, DecidableEq

end LoopVerifiedCompiler
