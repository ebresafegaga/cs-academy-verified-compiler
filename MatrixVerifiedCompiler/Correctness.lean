import MatrixVerifiedCompiler.Compiler

namespace MatrixVerifiedCompiler

/-! ## The delimiter discipline round-trips

`popMat` recovers exactly the matrix that `Mat.rowsOnto` laid out —
the two delimiters make the parse unambiguous. -/

/-- Reading a laid-out row: the values prepend onto the first row
opened by the `rowMark`. -/
theorem popMat_vals {t : Stack} {m : Mat} {s : Stack} (r : List Int)
    (h : popMat t = some (m, s)) :
    popMat (r.map .val ++ .rowMark :: t) = some (r :: m, s) := by
  induction r with
  | nil =>
    rw [List.map_nil, List.nil_append, popMat, h]
    rfl
  | cons a r ih =>
    rw [List.map_cons, List.cons_append, popMat, ih]
    rfl

/-- Popping a laid-out matrix recovers exactly that matrix and leaves
the rest of the stack alone. -/
theorem popMat_pushed (m : Mat) (s : Stack) :
    popMat (Mat.rowsOnto m (.endMark :: s)) = some (m, s) := by
  induction m with
  | nil => rfl
  | cons r m ih =>
    rw [Mat.rowsOnto]
    exact popMat_vals r ih

/-! ## Compiled code builds the layout -/

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

/-- Executing one row's code lays out that row. -/
theorem exec_compileRow (r : List Int) (p : List Instr) (stk : Stack) :
    exec (compileRow r ++ p) stk = exec p (r.map .val ++ .rowMark :: stk) := by
  rw [compileRow, List.cons_append, exec, exec_pushes]

/-- Executing all rows' code, emitted in reverse, lays out the rows
with row `0` on top. -/
theorem exec_rows (m : Mat) (p : List Instr) (base : Stack) :
    exec (m.reverse.flatMap compileRow ++ p) base = exec p (Mat.rowsOnto m base) := by
  induction m generalizing p with
  | nil => rfl
  | cons r m ih =>
    rw [List.reverse_cons, List.flatMap_append, List.append_assoc]
    rw [ih]
    simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil]
    rw [exec_compileRow, Mat.rowsOnto]

/-! ## Correctness -/

/-- Strengthened correctness lemma, conditional on the source
semantics succeeding: if `e` evaluates to the matrix `v`, then `e`'s
compiled code followed by any program `p` runs like `p` started with
`v`'s delimited segment on top of the stack. Ill-shaped expressions
(`eval = none`) are outside the claim. -/
theorem Expr.exec_compile_append (e : Expr) :
    ∀ (v : Mat), e.eval = some v → ∀ (p : List Instr) (stk : Stack),
      exec (e.compile ++ p) stk = exec p (Mat.rowsOnto v (.endMark :: stk)) := by
  induction e with
  | const n =>
    intro v hv p stk
    rw [eval] at hv
    injection hv with hv
    subst hv
    rw [compile]
    simp only [List.cons_append, List.nil_append]
    -- three machine steps: `endMark`, `rowMark`, `push n`
    rw [exec, exec, exec]
    simp only [Mat.rowsOnto, List.map_cons, List.map_nil, List.cons_append,
               List.nil_append]
  | vconst l =>
    intro v hv p stk
    rw [eval] at hv
    injection hv with hv
    subst hv
    rw [compile, List.cons_append]
    -- one `endMark` step, then the row's code
    rw [exec, exec_compileRow]
    simp only [Mat.rowsOnto]
  | mconst m =>
    intro v hv p stk
    rw [eval] at hv
    injection hv with hv
    subst hv
    rw [compile, List.cons_append]
    -- one `endMark` step, then all the rows' code
    rw [exec, exec_rows]
  | binop op e₁ e₂ ih₁ ih₂ =>
    intro v hv p stk
    rw [eval] at hv
    -- the source run must have evaluated both operands …
    cases h₁ : e₁.eval with
    | none => simp [h₁] at hv
    | some A =>
      cases h₂ : e₂.eval with
      | none => simp [h₁, h₂] at hv
      | some B =>
        -- … and applied the operator successfully
        rw [h₁, h₂] at hv
        simp at hv
        rw [compile]
        simp only [List.append_assoc, List.cons_append, List.nil_append]
        rw [ih₁ A h₁]               -- run `e₁`'s code: lays out segment `A`
        rw [ih₂ B h₂]               -- run `e₂`'s code: lays out segment `B`
        rw [exec]                   -- `binop` pops both segments …
        simp [popMat_pushed, hv]    -- … and lays out the result segment

/-- Compiler correctness: if the source semantics gives `e` the value
`v`, executing the compiled code on the empty stack terminates with
exactly `v`'s delimited segment as the stack. -/
theorem Expr.compile_correct (e : Expr) (v : Mat) (h : e.eval = some v) :
    exec e.compile [] = some (Mat.rowsOnto v [.endMark]) := by
  have hh := e.exec_compile_append v h [] []
  rw [List.append_nil] at hh
  rw [exec] at hh
  exact hh

end MatrixVerifiedCompiler
