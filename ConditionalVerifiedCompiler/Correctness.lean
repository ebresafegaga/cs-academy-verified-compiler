import ConditionalVerifiedCompiler.Compiler

namespace ConditionalVerifiedCompiler

/-- Where a jump lands, part 1: dropping exactly the length of `l₁`
from `l₁ ++ l₂` leaves `l₂`. This is `jmp` skipping over the
else-code. -/
theorem drop_length_append (l₁ l₂ : List α) :
    (l₁ ++ l₂).drop l₁.length = l₂ := by
  induction l₁ with
  | nil => rfl
  | cons a l ih => rw [List.cons_append, List.length_cons, List.drop_succ_cons, ih]

/-- Where a jump lands, part 2: dropping `l₁.length + 1` from
`l₁ ++ a :: l₂` skips the prefix and one further instruction,
leaving `l₂`. This is `jz` skipping over the then-code and the
trailing `jmp`. -/
theorem drop_length_succ_append (l₁ : List α) (a : α) (l₂ : List α) :
    (l₁ ++ a :: l₂).drop (l₁.length + 1) = l₂ := by
  induction l₁ with
  | nil => rfl
  | cons b l ih => rw [List.cons_append, List.length_cons, List.drop_succ_cons, ih]

/-- Strengthened correctness lemma: the compiled code for `e`,
followed by any program `p`, runs like `p` started with `e`'s value
pushed onto the stack.

Generalizing the statement over `p` and the initial stack is what
lets the induction hypotheses compose: subexpression code is always
followed by more code, and runs on intermediate stacks. -/
theorem Expr.exec_compile_append (e : Expr) (p : List Instr) (stk : Stack) :
    exec (e.compile ++ p) stk = exec p (e.eval :: stk) := by
  induction e generalizing p stk with
  | const n =>
    rw [compile]                -- the code is `[push n] ++ p`
    rw [List.singleton_append]  -- which is `push n :: p`
    rw [exec]                   -- one machine step: push `n`
    rw [eval]                   -- and `n` is the value of `const n`
  | binop op e₁ e₂ ih₁ ih₂ =>
    rw [compile]  -- the code is `(e₁.compile ++ e₂.compile ++ [binop op]) ++ p`
    -- reassociate `++` so that `e₁.compile` is the head of the
    -- program and everything after it is a single continuation
    rw [List.append_assoc (e₁.compile ++ e₂.compile) [Instr.binop op] p]
    rw [List.append_assoc e₁.compile e₂.compile ([Instr.binop op] ++ p)]
    rw [ih₁]                    -- run `e₁`'s code: it pushes `e₁.eval`
    rw [ih₂]                    -- run `e₂`'s code: it pushes `e₂.eval` on top
    rw [List.singleton_append]
    rw [exec]                   -- one machine step: pop `e₂.eval` and
                                -- `e₁.eval`, push the operation's result
    rw [eval]                   -- which is the value of the whole expression
  | ite c e₁ e₂ ihc ih₁ ih₂ =>
    rw [compile]  -- the code is `⟨c⟩ ++ [jz _] ++ ⟨e₁⟩ ++ [jmp _] ++ ⟨e₂⟩ ++ p`
    -- reassociate `++` and turn the singleton appends into `cons`,
    -- so that `c.compile` is the head of the program and each jump
    -- instruction is an explicit `cons` in front of what follows it
    simp only [List.append_assoc, List.cons_append, List.nil_append]
    rw [ihc]      -- run the condition's code: it pushes `c.eval`
    rw [exec]     -- one machine step: `jz` pops `c.eval` and decides
    rw [eval]     -- the expression's value is decided by `c.eval` too
    by_cases h : c.eval = 0
    · -- condition zero ("false"): `jz` jumps …
      rw [if_pos h, if_pos h]
      rw [drop_length_succ_append]  -- … over `e₁`'s code and the `jmp`,
                                    -- landing exactly at `e₂`'s code
      rw [ih₂]                      -- run `e₂`'s code: it pushes `e₂.eval`
    · -- condition nonzero ("true"): `jz` falls through
      rw [if_neg h, if_neg h]
      rw [ih₁]                      -- run `e₁`'s code: it pushes `e₁.eval`
      rw [exec]                     -- one machine step: `jmp` skips …
      rw [drop_length_append]       -- … exactly `e₂`'s code, landing at `p`

/-- Compiler correctness: executing a compiled expression on the
empty stack terminates, with exactly the expression's value as the
result. -/
theorem Expr.compile_correct (e : Expr) :
    exec e.compile [] = some [e.eval] := by
  have h := e.exec_compile_append [] []
  rw [List.append_nil] at h  -- `e.compile ++ []` is just `e.compile`
  rw [exec] at h             -- the empty program returns its stack
  exact h

end ConditionalVerifiedCompiler
