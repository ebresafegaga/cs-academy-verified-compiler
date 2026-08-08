namespace MatrixVerifiedCompiler

/-- Binary operators of the source language. -/
inductive BinOp where
  | add
  | sub
  | mul
  deriving Repr, DecidableEq

/-- A matrix: a list of rows. Nothing forces rectangularity; the
"shape" of a matrix is its row-length profile, and operations demand
matching profiles. -/
abbrev Mat := List (List Int)

/-- Abstract syntax: the vector language extended one rank up.
Semantically every value is a matrix: a scalar is `1 × 1` and a
vector is a single row — continuing the vector extension's
identification of ranks, which is what keeps the delimited stack
representation faithful. -/
inductive Expr where
  | const (n : Int)
  | vconst (l : List Int)
  | mconst (m : Mat)
  | binop (op : BinOp) (e₁ e₂ : Expr)
  deriving Repr, DecidableEq

end MatrixVerifiedCompiler
