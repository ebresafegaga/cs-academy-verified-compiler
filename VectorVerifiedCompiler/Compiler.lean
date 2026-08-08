import VectorVerifiedCompiler.Target

namespace VectorVerifiedCompiler

/-- Compile an expression. A constant becomes its delimited segment:
`mark` first, then the elements pushed last-to-first so that element
`0` ends up on top. Binary operations compile post-order, as in the
base language. -/
def Expr.compile : Expr → List Instr
  | .const n => [.mark, .push n]
  | .vconst l => .mark :: (l.reverse.map Instr.push)
  | .binop op e₁ e₂ => e₁.compile ++ e₂.compile ++ [.binop op]

end VectorVerifiedCompiler
