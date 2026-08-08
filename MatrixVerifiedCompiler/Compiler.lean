import MatrixVerifiedCompiler.Target

namespace MatrixVerifiedCompiler

/-- Code for one row: its `rowMark` first, then the elements pushed
last-to-first so element `0` ends up on top. -/
def compileRow (r : List Int) : List Instr :=
  .rowMark :: (r.reverse.map Instr.push)

/-- Compile an expression. A constant becomes its delimited segment:
the `endMark` first, then the rows emitted last-to-first so row `0`
ends up on top. Binary operations compile post-order, as always. -/
def Expr.compile : Expr → List Instr
  | .const n => [.endMark, .rowMark, .push n]
  | .vconst l => .endMark :: compileRow l
  | .mconst m => .endMark :: (m.reverse.flatMap compileRow)
  | .binop op e₁ e₂ => e₁.compile ++ e₂.compile ++ [.binop op]

end MatrixVerifiedCompiler
