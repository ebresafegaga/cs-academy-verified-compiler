import ConditionalVerifiedCompiler.Target

namespace ConditionalVerifiedCompiler

/-- Compile an expression to stack-machine code.

Constants and binary operations compile as in the base language. A
conditional compiles to the classic jump pattern:

```
    ⟨code for c⟩
    jz (|e₁'s code| + 1)   -- zero: jump past the then-code and the jmp
    ⟨code for e₁⟩
    jmp |e₂'s code|        -- skip the else-code
    ⟨code for e₂⟩
```
-/
def Expr.compile : Expr → List Instr
  | .const n => [.push n]
  | .binop op e₁ e₂ => e₁.compile ++ e₂.compile ++ [.binop op]
  | .ite c e₁ e₂ =>
      c.compile
        ++ [.jz (e₁.compile.length + 1)]
        ++ e₁.compile
        ++ [.jmp e₂.compile.length]
        ++ e₂.compile

end ConditionalVerifiedCompiler
