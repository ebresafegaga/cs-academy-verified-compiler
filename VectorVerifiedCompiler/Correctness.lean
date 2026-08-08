import VectorVerifiedCompiler.Compiler

namespace VectorVerifiedCompiler

/-- Popping a value that was pushed as a delimited segment recovers
exactly that value and leaves the rest of the stack alone. This is
the whole point of the delimiter. -/
theorem popValue_pushed (l : List Int) (s : Stack) :
    popValue (l.map .val ++ .mark :: s) = some (l, s) := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    rw [List.map_cons, List.cons_append, popValue, ih]
    rfl

/-- Executing the pushes for a list of elements, emitted in reverse,
puts the elements on the stack with the head on top. -/
theorem exec_pushes (l : List Int) (p : List Instr) (stk : Stack) :
    exec (l.reverse.map Instr.push ++ p) stk = exec p (l.map .val ++ stk) := by
  induction l generalizing p stk with
  | nil => rfl
  | cons a l ih =>
    rw [List.reverse_cons, List.map_append, List.append_assoc]
    rw [ih]
    simp only [List.map_cons, List.map_nil, List.singleton_append]
    rw [exec, List.cons_append]

/-- Strengthened correctness lemma, conditional on the source
semantics succeeding: if `e` evaluates to the vector `v`, then `e`'s
compiled code followed by any program `p` runs like `p` started with
`v`'s delimited segment on top of the stack. Ill-shaped expressions
(`eval = none`) are outside the claim. -/
theorem Expr.exec_compile_append (e : Expr) :
    ∀ (v : List Int), e.eval = some v → ∀ (p : List Instr) (stk : Stack),
      exec (e.compile ++ p) stk = exec p (v.map .val ++ .mark :: stk) := by
  induction e with
  | const n =>
    intro v hv p stk
    rw [eval] at hv
    injection hv with hv
    subst hv
    rw [compile]
    simp only [List.cons_append, List.nil_append, List.map_cons, List.map_nil]
    -- two machine steps: `mark`, then `push n`
    rw [exec, exec]
  | vconst l =>
    intro v hv p stk
    rw [eval] at hv
    injection hv with hv
    subst hv
    rw [compile]
    simp only [List.cons_append]
    -- one `mark` step, then the run of pushes
    rw [exec, exec_pushes]
  | binop op e₁ e₂ ih₁ ih₂ =>
    intro v hv p stk
    rw [eval] at hv
    -- the source run must have evaluated both operands …
    cases h₁ : e₁.eval with
    | none => simp [h₁] at hv
    | some xs =>
      cases h₂ : e₂.eval with
      | none => simp [h₁, h₂] at hv
      | some ys =>
        -- … and applied the operator successfully
        rw [h₁, h₂] at hv
        simp at hv
        rw [compile]
        simp only [List.append_assoc, List.cons_append, List.nil_append]
        rw [ih₁ xs h₁]                -- run `e₁`'s code: pushes segment `xs`
        rw [ih₂ ys h₂]                -- run `e₂`'s code: pushes segment `ys`
        rw [exec]                     -- `binop` pops both segments …
        simp [popValue_pushed, hv]    -- … and pushes the result segment

/-- Compiler correctness: if the source semantics gives `e` the value
`v`, executing the compiled code on the empty stack terminates with
exactly `v`'s delimited segment as the stack. -/
theorem Expr.compile_correct (e : Expr) (v : List Int) (h : e.eval = some v) :
    exec e.compile [] = some (v.map .val ++ [.mark]) := by
  have hh := e.exec_compile_append v h [] []
  rw [List.append_nil] at hh
  rw [exec] at hh
  exact hh

end VectorVerifiedCompiler
