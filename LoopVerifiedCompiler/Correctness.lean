import LoopVerifiedCompiler.Compiler

namespace LoopVerifiedCompiler

/-! ## List lemmas: what the machine finds at a given pc

With a pc-based machine, the basic facts are about indexing into
appended code, not about dropping it. -/

/-- Indexing right past a prefix finds the first instruction after
it. -/
theorem getElem?_append_length (l₁ : List α) (a : α) (l₂ : List α) :
    (l₁ ++ a :: l₂)[l₁.length]? = some a := by
  induction l₁ with
  | nil => rfl
  | cons b l ih => rw [List.cons_append, List.length_cons, List.getElem?_cons_succ, ih]

/-- Indexing can be pushed past a prefix. -/
theorem getElem?_append_add (l₁ l₂ : List α) (n : Nat) :
    (l₁ ++ l₂)[l₁.length + n]? = l₂[n]? := by
  induction l₁ with
  | nil => rw [List.nil_append, List.length_nil, Nat.zero_add]
  | cons b l ih =>
    rw [List.cons_append, List.length_cons, Nat.add_right_comm,
        List.getElem?_cons_succ, ih]

/-- Replace the (purely arithmetic) program counters of a run by
equal ones — the glue for joining runs whose pc expressions are equal
but not syntactically identical. -/
theorem Steps.cast_pc {P : List Instr} {stk stk' : Stack} {st st' : State}
    (h : Steps P (i, stk, st) (j, stk', st'))
    (hi : i = i') (hj : j = j') : Steps P (i', stk, st) (j', stk', st') := by
  rw [← hi, ← hj]
  exact h

/-! ## Correctness

Both lemmas are stated for compiled code embedded in an arbitrary
program `P₁ ++ code ++ P₂`, starting at `pc = P₁.length`. This
generalization is what lets runs of subterms compose: a subterm's
code always sits between other code. -/

/-- Running a compiled expression: from the start of `e`'s code the
machine walks to its end, pushing `e`'s value; state untouched. -/
theorem Expr.steps_compile (e : Expr) (P₁ P₂ : List Instr) (stk : Stack) (st : State) :
    Steps (P₁ ++ e.compile ++ P₂) (P₁.length, stk, st)
      (P₁.length + e.compile.length, e.eval st :: stk, st) := by
  induction e generalizing P₁ P₂ stk with
  | const n =>
    rw [compile, eval]
    simp only [List.append_assoc, List.cons_append, List.nil_append,
               List.length_cons, List.length_nil, Nat.zero_add]
    -- a single `push` step
    exact Steps.single (Step.push (getElem?_append_length P₁ _ P₂))
  | var x =>
    rw [compile, eval]
    simp only [List.append_assoc, List.cons_append, List.nil_append,
               List.length_cons, List.length_nil, Nat.zero_add]
    -- a single `load` step
    exact Steps.single (Step.load (getElem?_append_length P₁ _ P₂))
  | binop op e₁ e₂ ih₁ ih₂ =>
    rw [compile, eval]
    simp only [List.append_assoc, List.cons_append, List.nil_append,
               List.length_append, List.length_cons, List.length_nil,
               Nat.zero_add]
    -- run `e₁`'s code (its continuation is everything after it)
    have h₁ := ih₁ P₁ (e₂.compile ++ (Instr.binop op :: P₂)) stk
    simp only [List.append_assoc] at h₁
    -- run `e₂`'s code, on the stack holding `e₁`'s value
    have h₂ := ih₂ (P₁ ++ e₁.compile) (Instr.binop op :: P₂) (e₁.eval st :: stk)
    simp only [List.append_assoc, List.length_append] at h₂
    -- the `binop` instruction sits right after both codes
    have h₃ : Step (P₁ ++ (e₁.compile ++ (e₂.compile ++ (Instr.binop op :: P₂))))
        (P₁.length + (e₁.compile.length + e₂.compile.length),
          e₂.eval st :: e₁.eval st :: stk, st)
        (P₁.length + (e₁.compile.length + e₂.compile.length) + 1,
          op.denote (e₁.eval st) (e₂.eval st) :: stk, st) :=
      Step.binop (by
        rw [getElem?_append_add, getElem?_append_add]
        exact getElem?_append_length e₂.compile _ P₂)
    exact Steps.trans h₁ (Steps.trans h₂
      (Steps.cast_pc (Steps.single h₃) (by omega) (by omega)))

/-- Running a compiled statement: if the source big-step semantics
takes `st` to `st'`, then from the start of the compiled code the
machine walks to its end, transforming the state the same way and
leaving the stack alone. Induction is on the big-step derivation —
in particular a `whileTrue` derivation contains a derivation for the
*rest* of the loop, which is what the backward jump replays. -/
theorem Stmt.steps_compile {s : Stmt} {st st' : State} (h : BigStep s st st') :
    ∀ (P₁ P₂ : List Instr) (stk : Stack),
      Steps (P₁ ++ s.compile ++ P₂) (P₁.length, stk, st)
        (P₁.length + s.compile.length, stk, st') := by
  induction h with
  | skip =>
    intro P₁ P₂ stk
    rw [compile]
    simp only [List.append_nil, List.length_nil, Nat.add_zero]
    -- no code, no steps
    exact Steps.refl
  | @assign st x e =>
    intro P₁ P₂ stk
    rw [compile]
    simp only [List.append_assoc, List.cons_append, List.nil_append,
               List.length_append, List.length_cons, List.length_nil,
               Nat.zero_add]
    -- run `e`'s code, pushing its value …
    have h₁ := Expr.steps_compile e P₁ (Instr.store x :: P₂) stk st
    simp only [List.append_assoc] at h₁
    -- … then one `store` step pops it into the state
    have h₂ : Step (P₁ ++ (e.compile ++ (Instr.store x :: P₂)))
        (P₁.length + e.compile.length, e.eval st :: stk, st)
        (P₁.length + e.compile.length + 1, stk, st.update x (e.eval st)) :=
      Step.store (by
        rw [getElem?_append_add]
        exact getElem?_append_length e.compile _ P₂)
    exact Steps.trans h₁ (Steps.cast_pc (Steps.single h₂) rfl (by omega))
  | @seq s₁ s₂ st st' st'' h₁ h₂ ih₁ ih₂ =>
    intro P₁ P₂ stk
    rw [compile]
    simp only [List.append_assoc, List.length_append]
    -- run `s₁`'s code, then `s₂`'s code right after it
    have g₁ := ih₁ P₁ (s₂.compile ++ P₂) stk
    simp only [List.append_assoc] at g₁
    have g₂ := ih₂ (P₁ ++ s₁.compile) P₂ stk
    simp only [List.append_assoc, List.length_append] at g₂
    exact Steps.trans g₁ (Steps.cast_pc g₂ rfl (by omega))
  | @whileFalse c body st hc =>
    intro P₁ P₂ stk
    rw [compile]
    simp only [List.append_assoc, List.cons_append, List.nil_append,
               List.length_append, List.length_cons, List.length_nil,
               Nat.zero_add]
    -- run the condition's code; by `hc` it pushes `0`
    have g₁ := Expr.steps_compile c P₁
      (Instr.jz (body.compile.length + 1) ::
        (body.compile ++
          (Instr.jmpBack (c.compile.length + body.compile.length + 2) :: P₂)))
      stk st
    rw [hc] at g₁
    simp only [List.append_assoc] at g₁
    -- `jz` pops the `0` and jumps past the body and the `jmpBack`,
    -- which is exactly the end of the loop's code
    have g₂ : Step (P₁ ++ (c.compile ++
          (Instr.jz (body.compile.length + 1) ::
            (body.compile ++
              (Instr.jmpBack (c.compile.length + body.compile.length + 2) :: P₂)))))
        (P₁.length + c.compile.length, 0 :: stk, st)
        (P₁.length + c.compile.length + 1 + (body.compile.length + 1), stk, st) :=
      Step.jzTaken (by
        rw [getElem?_append_add]
        exact getElem?_append_length c.compile _ _)
    exact Steps.trans g₁ (Steps.cast_pc (Steps.single g₂) rfl (by omega))
  | @whileTrue c body st st' st'' hc hbody hrest ih_body ih_rest =>
    intro P₁ P₂ stk
    rw [compile]
    simp only [List.append_assoc, List.cons_append, List.nil_append,
               List.length_append, List.length_cons, List.length_nil,
               Nat.zero_add]
    -- run the condition's code; it pushes a nonzero value
    have g₁ := Expr.steps_compile c P₁
      (Instr.jz (body.compile.length + 1) ::
        (body.compile ++
          (Instr.jmpBack (c.compile.length + body.compile.length + 2) :: P₂)))
      stk st
    simp only [List.append_assoc] at g₁
    -- `jz` pops it and falls through into the body
    have g₂ : Step (P₁ ++ (c.compile ++
          (Instr.jz (body.compile.length + 1) ::
            (body.compile ++
              (Instr.jmpBack (c.compile.length + body.compile.length + 2) :: P₂)))))
        (P₁.length + c.compile.length, c.eval st :: stk, st)
        (P₁.length + c.compile.length + 1, stk, st) :=
      Step.jzNotTaken (by
        rw [getElem?_append_add]
        exact getElem?_append_length c.compile _ _) hc
    -- run the body's code (by the body's induction hypothesis)
    have g₃ := ih_body (P₁ ++ c.compile ++ [Instr.jz (body.compile.length + 1)])
      (Instr.jmpBack (c.compile.length + body.compile.length + 2) :: P₂) stk
    simp only [List.append_assoc, List.cons_append, List.nil_append,
               List.length_append, List.length_cons, List.length_nil,
               Nat.zero_add] at g₃
    -- `jmpBack` returns to the very start of the loop's code
    have g₄ : Step (P₁ ++ (c.compile ++
          (Instr.jz (body.compile.length + 1) ::
            (body.compile ++
              (Instr.jmpBack (c.compile.length + body.compile.length + 2) :: P₂)))))
        (P₁.length + (c.compile.length + (body.compile.length + 1)), stk, st')
        (P₁.length + (c.compile.length + (body.compile.length + 1)) + 1
          - (c.compile.length + body.compile.length + 2), stk, st') :=
      Step.jmpBack (by
        rw [getElem?_append_add, getElem?_append_add, List.getElem?_cons_succ]
        exact getElem?_append_length body.compile _ P₂)
    -- and the rest of the loop runs from there (induction hypothesis
    -- on the remaining derivation — this is where the loop "repeats")
    have g₅ := ih_rest P₁ P₂ stk
    rw [compile] at g₅
    simp only [List.append_assoc, List.cons_append, List.nil_append,
               List.length_append, List.length_cons, List.length_nil,
               Nat.zero_add] at g₅
    exact Steps.trans g₁ (Steps.trans (Steps.single g₂) (Steps.trans g₃
      (Steps.trans (Steps.cast_pc (Steps.single g₄) (by omega) (by omega)) g₅)))

/-- Compiler correctness: a terminating source run is replayed by the
machine — from pc `0` and an empty stack, execution reaches the end
of the compiled program with an empty stack and the same final
state. -/
theorem Stmt.compile_correct {s : Stmt} {st st' : State} (h : BigStep s st st') :
    Steps s.compile (0, [], st) (s.compile.length, [], st') := by
  have hs := Stmt.steps_compile h [] [] []
  simpa using hs

end LoopVerifiedCompiler
