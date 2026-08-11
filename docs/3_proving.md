# Lesson 3: Certification & Proofs

Welcome to Lesson 3! You’ve built a compiler that turns abstract math trees into machine code. It *looks* like it works. We could test it on `3 + 4` or `10 * (2 - 1)`, and it would give the right answer. 

But what if there is a bug that only happens on trees that are 100 levels deep? Or only when a multiplication is followed by two additions? 

In this lesson, we transition from Software Engineers to Mathematicians. We are going to use Lean's power as a **Theorem Prover** to mathematically guarantee our compiler *never* makes a mistake.

## Why Prove Anything?

### Concept: Testing vs. Proving

In standard software engineering, we write Unit Tests. We give a function some inputs and check the outputs. 
But as computer scientist Edsger W. Dijkstra famously said: 
> *"Program testing can be used to show the presence of bugs, but never to show their absence."*

There are **infinite** possible expressions. You can always add one more `+ 1` to a tree. Therefore, no matter how many unit tests you write, you can never test every possible input. We need a mathematical proof to cover the concept of "infinity".

### Concept: Lean as a Theorem Prover

Why did we use Lean for this project? Why not Python or Java? Lean is purely functional—meaning variables never change state—which allows us to treat code like mathematical equations. 

Because of this, Lean's true purpose isn't just to write code; it is designed to write **Proofs**. The goal of a proof is to use strict mathematical logic to show that a statement is universally true or false. In traditional math, you do this with a pencil and paper, and it's easy to make a small logical error. In Lean, we use code to *ensure* our logic is completely flawless. If our proof has a hole in it, Lean simply refuses to compile.

### Concept: Theorems vs. Proofs

In math, a **Theorem** is a statement that we claim is true. For example: "The sum of two even numbers is always even." 
A **Proof** is the step-by-step logical argument that actually demonstrates *why* the theorem is true.

Let's state the main Theorem we want to prove for our compiler:
If we take *any* expression `e`, compile it, and run it on an empty stack `[]`, we should get the exact same answer as if we just evaluated `e` directly.

In Lean, we write the theorem statement like a function signature:
```lean
theorem Expr.compile_correct (e : Expr) : 
    exec e.compile [] = some [e.eval]
```

The `theorem` keyword is just like `def`. But instead of returning a normal value like an `Int`, it returns a mathematical proof. The "code" we write inside the theorem's body is the actual **proof**. 

## The Tactics Toolbox

Lean proofs are written interactively using **Tactics**. 
The whole point of an interactive proof is that you can't just prove everything at once. The Lean interface acts like a puzzle game. You start with a big "Goal" (your theorem), and you use tactics to manipulate the equation, splitting the problem into smaller, manageable steps, until the left side perfectly matches the right side.

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

How do we prove something works for an **infinite** number of possible expressions? We can't test them all one by one. Instead, we use a mathematical superpower called **Induction**.

#### The Domino Effect
To build your intuition for induction, imagine an infinitely long line of dominoes. If I ask you to prove that *every single domino will fall*, how would you do it? You only need to prove two things:

1. **The Base Case:** You knock over the very first domino.
2. **The Inductive Step:** You prove a rule: *If* a domino falls, it is positioned perfectly to knock over the next one.

If you prove those two rules, you have mathematically proven the entire infinite line will fall. You don't have to check the 100th domino or the 1,000,000th domino. The logic guarantees it.

#### Induction on Trees
Our AST `Expr` isn't a straight line of dominoes; it's a branching tree. But the exact same logic applies! This is called **Structural Induction**. We build our proof from the bottom up.

Instead of dominoes, imagine building a complex Lego structure. 
1. **The Base Case:** Prove that the simplest, most basic building blocks (the leaves of our tree) work correctly. For our compiler, the leaves are always constant numbers (`.const n`). 
2. **The Inductive Step:** We write a rule for combining pieces. We say: *Assume* that the left branch and the right branch are already working perfectly (we call this assumption the **Induction Hypothesis**). Now, prove that if you connect two working branches with a binary operator (`.binop`), the new bigger piece also works perfectly.

Why does this work? Let's look at the expression `(3 + 4) * 5`:
- First, we know `3`, `4`, and `5` compile correctly because they are Base Cases. 
- Next, look at the `+` branch. Because its children (`3` and `4`) compiled correctly, our Inductive Step guarantees the `+` branch will also compile correctly!
- Finally, look at the `*` branch. Because its children (the `+` branch and `5`) compiled correctly, our Inductive Step guarantees the `*` branch will compile correctly!

By proving just the Base Case and the Inductive Step, a chain reaction of logic travels from the bottom of the tree all the way to the top. If the leaves are correct, and every branch built on them correctly combines them, the whole infinite tree must be correct!

### The Direct Approach: Why It Fails

Let's open up `Correctness.lean` and try to prove our theorem directly using induction.

```lean
theorem Expr.compile_correct (e : Expr) : 
    exec e.compile [] = some [e.eval] := by
  induction e with
  | const n =>
    -- Base Case: this is easy!
    rw [compile]  -- exec [.push n] []
    rw [exec]     -- some [n]
    rw [eval]     -- some [n]
  | binop op e₁ e₂ ih₁ ih₂ =>
    -- Inductive Step: Here is where we get stuck!
    rw [compile] 
    -- Goal: exec (e₁.compile ++ e₂.compile ++ [.binop op]) [] = some [op.denote e₁.eval e₂.eval]
```

We hit a massive snag. Our Induction Hypothesis `ih₁` says that `exec e₁.compile [] = some [e₁.eval]`. It *only* works if the stack is completely empty `[]` and there is no other code running after it.

But look at our goal! We are trying to run `exec (e₁.compile ++ e₂.compile ++ [.binop op]) []`.
Because our compiler chains lists together with `++`, when `e₁` finishes executing, the machine immediately needs to execute `e₂` and the `binop`. We can't use our induction hypothesis because it doesn't match the situation!

> 🤔 **Thinking Block**
>
> Think about how a stack machine actually works. When it finishes running `e₁.compile`, is the stack empty? No! It has the result of `e₁` sitting on it. When it starts running `e₂.compile`, the stack already has something on it!

### Concept: Strengthening the Theorem

To solve this, we need to discover a key intuition in mathematics: **Sometimes it is easier to prove a harder problem.** 

Our main theorem is too weak. It only talks about empty stacks and programs running in isolation. We need to **strengthen** our claim. We need a helper theorem (a **lemma**) that proves our compiler works *no matter what is already on the stack*, and *no matter what code comes after it*!

If we can prove that running `e.compile ++ p` (our compiled code followed by some extra program `p`) on *any* starting stack `stk` behaves perfectly, then we can easily solve our main theorem just by plugging in `[]` for `p` and `[]` for `stk`.

> 💡 **HINT: Lemma Toolbox**
> You'll need some math facts about lists to complete this proof. You can't guess these names, so here they are:
> - `List.singleton_append`: Proves that `[x] ++ list` is the same as `x :: list`.
> - `List.append_assoc`: Proves that `(A ++ B) ++ C` is the same as `A ++ (B ++ C)`.
> - `List.append_nil`: Proves that `list ++ []` is just `list`.

### Proving the Helper Lemma

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
>   -- Notice `generalizing p stk`: this allows our lists to change during the proof!
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
>     -- ih₁ and ih₂ are our incredibly strong Induction Hypotheses!
>     -- They work for ANY stack and ANY following program.
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