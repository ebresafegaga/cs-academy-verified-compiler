import VerifiedCompiler.Target

namespace VerifiedCompiler

/-- Compile an expression to stack-machine code by post-order
traversal: code for the left operand, code for the right operand
(leaving its value on top of the stack), then the operator. -/
def Expr.compile : Expr → List Instr
  | .const n => [.push n]
  | .binop op e₁ e₂ => e₁.compile ++ e₂.compile ++ [.binop op]

end VerifiedCompiler
