import BaseVerifiedCompiler.Compiler

namespace BaseVerifiedCompiler

/-- Strengthened correctness lemma: the compiled code for `e`,
followed by any program `p`, runs like `p` started with `e`'s value
pushed onto the stack.

Generalizing the statement over `p` and the initial stack is what
lets the induction hypotheses compose: in the `binop` case, `e₁`'s
code is followed by more code (`e₂`'s and the operator) and `e₂`'s
code runs on a non-empty stack (`e₁`'s value is already there). -/
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

/-- Compiler correctness: executing a compiled expression on the
empty stack terminates, with exactly the expression's value as the
result. -/
theorem Expr.compile_correct (e : Expr) :
    exec e.compile [] = some [e.eval] := by
  have h := e.exec_compile_append [] []
  rw [List.append_nil] at h  -- `e.compile ++ []` is just `e.compile`
  rw [exec] at h             -- the empty program returns its stack
  exact h

end BaseVerifiedCompiler
