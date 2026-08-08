import LoopVerifiedCompiler.Target

namespace LoopVerifiedCompiler

/-- Compile an expression: code that pushes the expression's value
onto the stack, leaving the state untouched. -/
def Expr.compile : Expr → List Instr
  | .const n => [.push n]
  | .var x => [.load x]
  | .binop op e₁ e₂ => e₁.compile ++ e₂.compile ++ [.binop op]

/-- Compile a statement: code that transforms the state, leaving the
stack as it found it. A loop compiles to the classic pattern:

```
    ⟨code for c⟩
    jz (|body code| + 1)     -- zero: jump past the body and the jmpBack
    ⟨code for body⟩
    jmpBack (|c code| + |body code| + 2)   -- back to the condition
```
-/
def Stmt.compile : Stmt → List Instr
  | .skip => []
  | .assign x e => e.compile ++ [.store x]
  | .seq s₁ s₂ => s₁.compile ++ s₂.compile
  | .whileDo c body =>
      c.compile
        ++ [.jz (body.compile.length + 1)]
        ++ body.compile
        ++ [.jmpBack (c.compile.length + body.compile.length + 2)]

end LoopVerifiedCompiler
