# Lesson 3: Certification & Proofs

Welcome to Lesson 3! You’ve built a compiler that turns abstract math trees into machine code. It *looks* like it works. We could test it on `3 + 4` or `10 * (2 - 1)`, and it would give the right answer. 

But what if there is a bug that only happens on trees that are 100 levels deep? Or only when a multiplication is followed by two additions? 

In this lesson, we transition from Software Engineers to Mathematicians. We are going to use Lean's power as a **Theorem Prover** to mathematically guarantee our compiler *never* makes a mistake.

## Why Prove Anything?

### Concept: Testing vs. Proving

In standard software engineering, we write Unit Tests. We give a function some inputs and check the outputs. 
But as computer scientist Edsger W. Dijkstra famously said: 
> *"Program testing can be used to show the presence of bugs, but never to show their absence."*

> 🧠 **Check My Thinking: The Limits of Testing**
> 
> How many possible `Expr` (Abstract Syntax Trees) exist? Could we write a test for every single one?

<details>
<summary>Answer</summary>

> There are **infinite** possible expressions. You can always add one more `+ 1` to a tree. Therefore, no matter how many unit tests you write, you can never test every possible input. We need a mathematical proof to cover the concept of "infinity".
</details>

### Concept: The Main Theorem

Let's state what we want to prove. 
If we take *any* expression `e`, compile it, and run it on an empty stack `[]`, we should get the exact same answer as if we just evaluated `e` directly.

In Lean, we write this as a **Theorem**:
```lean
theorem Expr.compile_correct (e : Expr) : 
    exec e.compile [] = some [e.eval]

```

Think of a theorem like a function signature. The `theorem` keyword is just like `def`, but instead of returning a value, it returns a mathematical proof. The "code" we write inside the theorem is the **proof**. If our proof is wrong, Lean simply won't compile.

## The Tactics Toolbox

Lean proofs are written using **Tactics**. Think of the proof window in Lean as a puzzle game. You start with a "Goal" (your theorem), and you use tactics to manipulate the equation until the left side perfectly matches the right side. 

> 📘 **LEAN SYNTAX: Tactic Mode**
> When you see the `by` keyword, it means Lean is switching from "Programming Mode" to "Tactic Mode" (the puzzle game). 
> When we use tactics like `rw`, we put the rules we want to rewrite with in square brackets, like `rw [compile]`.

### Concept: The `rw` (Rewrite) Tactic

Our main tool in this lesson is `rw` (rewrite). It substitutes equals for equals.
If we know that `A = B`, and we have an equation `A + 1 = 5`, we can use `rw` to turn it into `B + 1 = 5`.

We can also use `rw` to "unfold" our functions.
If we write `rw [compile]`, Lean will look at how we defined the `compile` function in Lesson 2, and replace the word `compile` with the actual code we wrote!

> 🤔 **Thinking Block**
>
> If `e` is a `.const n`, what will the equation `exec e.compile []` look like after we use the tactic `rw [compile]`?

<details>
<summary>Answer</summary>

> From Lesson 2, we know `.const n` compiles to `[.push n]`.
> So, it will rewrite `e.compile` into `[.push n]`, resulting in:
> `exec [.push n] []`
</details>


## Proving Compiler Correctness

### Concept: Structural Induction

How do we prove something for an infinite number of trees? We use **Induction**.
Induction has two steps:

1. **The Base Case:** Prove it works for the simplest part of the tree (the leaves). For us, that's `.const n`.
2. **The Inductive Step:** Assume it works for the left and right branches (we call this the *Induction Hypothesis*). Prove that if the branches work, combining them with a `.binop` also works.

If the leaves are correct, and every branch built on them is correct, the whole infinite tree must be correct!

> 📘 **LEAN SYNTAX: Induction Magic**
> In the code below, you'll see `generalizing p stk`. This is advanced Lean magic that allows our lists to change during the proof. Don't worry about how it works under the hood right now—just know it's required here.
> Also, when we write `| binop op e₁ e₂ ih₁ ih₂ =>`, Lean automatically creates our Induction Hypotheses and binds them to the names `ih₁` and `ih₂` for us to use!

### Concept: The Helper Lemma

We hit a snag. When we compile a `binop e1 e2`, the code is `e1.compile ++ e2.compile ++ [.binop op]`.
When the machine runs `e2.compile`, the stack **is not empty**! It already has the result of `e1` sitting on it. Also, there is more code coming after it (the `binop`).

Our main theorem only talks about an *empty* stack and *no* extra code. We need a stronger helper theorem (a **lemma**) that proves our compiler works no matter what is already on the stack, and no matter what code comes after!

> 💡 **HINT: Lemma Toolbox**
> You'll need some math facts about lists to complete this proof. You can't guess these names, so here they are:
> - `List.singleton_append`: Proves that `[x] ++ list` is the same as `x :: list`.
> - `List.append_assoc`: Proves that `(A ++ B) ++ C` is the same as `A ++ (B ++ C)`.
> - `List.append_nil`: Proves that `list ++ []` is just `list`.

> 💻 **ACTION: Open `Correctness.lean`**
>
> Let's write the `exec_compile_append` lemma. We've set up the induction for you.
> Your job is to fill in the `rw` tactics based on the comments.
>
> **Skeleton:**
> ```lean
> import BaseVerifiedCompiler.Compiler
> namespace BaseVerifiedCompiler
> 
> theorem Expr.exec_compile_append (e : Expr) (p : List Instr) (stk : Stack) :
>     exec (e.compile ++ p) stk = exec p (e.eval :: stk) := by
>   induction e generalizing p stk with
>   | const n =>
>     -- We want to unfold how `compile` works for a const
>     rw [compile]                 
>     -- Lean needs help simplifying the list append: `[push n] ++ p` -> `push n :: p`
>     rw [List.singleton_append]   
>     -- Now unfold how the machine `exec`utes a push instruction
>     -- YOUR TURN: Write a rw tactic to unfold `exec`
>     
>     -- Finally, unfold how a const `eval`uates to finish the proof!
>     -- YOUR TURN: Write a rw tactic to unfold `eval`
>     
>   | binop op e₁ e₂ ih₁ ih₂ =>
>     rw [compile]  -- Unfold compile
>     -- Reassociate the lists so Lean reads them in the right order
>     rw [List.append_assoc (e₁.compile ++ e₂.compile) [Instr.binop op] p]
>     rw [List.append_assoc e₁.compile e₂.compile ([Instr.binop op] ++ p)]
>     
>     -- ih₁ and ih₂ are our Induction Hypotheses (our assumption that e1 and e2 work)
>     -- Let's run e1's code by rewriting with ih₁
>     rw [ih₁]                    
>     -- YOUR TURN: Run e2's code by rewriting with its induction hypothesis!
>     
>     rw [List.singleton_append]
>     -- YOUR TURN: Unfold how the machine `exec`utes a binop instruction
>     
>     -- YOUR TURN: Unfold how a binop `eval`uates to finish the proof!
> ```

<details>
<summary>Answer</summary>

```lean
theorem Expr.exec_compile_append (e : Expr) (p : List Instr) (stk : Stack) :
    exec (e.compile ++ p) stk = exec p (e.eval :: stk) := by
  induction e generalizing p stk with
  | const n =>
    rw [compile]                -- the code is `[push n] ++ p`
    rw [List.singleton_append]  -- which is `push n :: p`
    rw [exec]                   -- one machine step: push `n`
    rw [eval]                   -- and `n` is the value of `const n`
  | binop op e₁ e₂ ih₁ ih₂ =>
    rw [compile]  
    rw [List.append_assoc (e₁.compile ++ e₂.compile) [Instr.binop op] p]
    rw [List.append_assoc e₁.compile e₂.compile ([Instr.binop op] ++ p)]
    rw [ih₁]                    -- run `e₁`'s code: it pushes `e₁.eval`
    rw [ih₂]                    -- run `e₂`'s code: it pushes `e₂.eval` on top
    rw [List.singleton_append]
    rw [exec]                   -- one machine step: pop `e₂.eval` and `e₁.eval`
    rw [eval]                   -- which is the value of the whole expression
```
</details>

### The Final Boss: Proving the Main Theorem

We have our super-strong lemma. Now we just apply it to our specific case: an empty stack `[]` and an empty extra program `[]`.

> 💻 **ACTION: Stay in `Correctness.lean`**
>
> Let's finish the compiler! Use the lemma we just proved (`exec_compile_append`) to prove the main theorem.
>
> 📘 **LEAN SYNTAX: have, at, and exact**
> - **`have`:** The `have h := ...` tactic creates a local variable/fact named `h` that you can use in your proof.
> - **`at`:** By default, `rw` alters your main Goal. Adding `at h` tells Lean to rewrite your local hypothesis `h` instead.
> - **`exact`:** If your hypothesis perfectly matches the Goal, you use `exact h` to tell Lean "this is exactly what you asked for!" and win the game.
>
> **Skeleton:**
> ```lean
> theorem Expr.compile_correct (e : Expr) :
>     exec e.compile [] = some [e.eval] := by
>   -- Create a local fact `h` by calling our lemma with empty lists
>   have h := e.exec_compile_append [] []
>   
>   -- Clean up the left side: `e.compile ++ []` is just `e.compile`
>   rw [List.append_nil] at h  
>   
>   -- Clean up the right side: executing an empty program returns its stack
>   -- YOUR TURN: Write a rw tactic to unfold `exec` at h
>   
>   -- Since `h` is now exactly our goal, tell Lean we are done!
>   exact h
> ```

<details>
<summary>Answer</summary>

```lean
theorem Expr.compile_correct (e : Expr) :
    exec e.compile [] = some [e.eval] := by
  have h := e.exec_compile_append [] []
  rw [List.append_nil] at h  -- `e.compile ++ []` is just `e.compile`
  rw [exec] at h             -- the empty program returns its stack
  exact h

end BaseVerifiedCompiler

```
</details>

### 🎉 You Did It!

If Lean shows "No goals", you have mathematically proven your compiler is perfectly correct. It is physically impossible for your compiler to produce the wrong sequence of stack instructions for *any* valid math expression in the universe.