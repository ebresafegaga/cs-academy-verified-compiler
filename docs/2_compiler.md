# Lesson 2: Evaluators & The Compiler

In the previous lesson, we built the blueprints for our language. We defined `Expr` (our Source AST) and `Instr` (our Target Stack instructions). 

But right now, they are just empty shapes. `(3 + 4)` is just a tree; it doesn't actually compute the number `7`. In this lesson, we are going to write **Evaluators** to give meaning to our code, and then build the **Compiler** that translates our AST into Stack Machine instructions!

## Concept: Evaluator vs. Compiler (The Big Picture)

What's the difference between an Evaluator and a Compiler, and why are we building both? This is the entire purpose of this project!

**The Evaluator (High-Level):**
An Evaluator takes our high-level `Expr` tree and just runs it directly to give you a final answer. For example, if we evaluate the AST for `(3 + 4)`, it just looks at it and says "Ah, 7." It is essentially a calculator. But notice what the Evaluator *doesn't* do: it doesn't know anything about our Stack Machine. It doesn't know what "push" or "pop" is. It just gives the answer.

**The Compiler (The Translation):**
Our true goal is that we MUST run our code on our target Stack Machine. We can't just evaluate it; we need to generate machine code. The **Compiler** is the translator that tells us *how* to run our AST on the Stack Machine. 

But what if our translation is wrong? In a normal programming language, there is no mathematical law saying that a `+` node must translate to a push and a pop. What if our compiler accidentally translates `+` into the `-` instruction? 

**The Total Goal:**
We are going to write the Evaluator (the true mathematical answer), the Compiler (the translation), and a Simulator (a function that runs the Stack Machine instructions). 

In Lesson 3, we will mathematically prove that in *every single possible path*, evaluating an expression directly gives the exact same result as compiling it and then simulating it on the stack. 

Note that verifying is different than testing. We could write a test to check if `3 + 4` compiles correctly. But what about `3 + 4 + 1`? What about an expression with a million additions? You can never write enough tests. Lean has special logic in its inductive types (which we'll use in Lesson 3) to help us prove that this translation is 100% correct, no matter what infinitely large program we throw at it!

## The Expression Evaluator

We need to tell Lean how to find the mathematical value of an `Expr`. In programming language theory, we call this the **Semantics** (the meaning) of the language.

### Concept: Functions
Before we evaluate our AST, how do we write functions in Lean?

This is a little different than functions in other languages (like Python or Java). In Lean, we don't write "steps" one by one (like `step 1: do this`, `step 2: return that`). Instead, a function is just a single big expression that evaluates to a result.

Here is a complete example of defining a function that calculates the area of a rectangle:

```lean
def area (width : Int) (height : Int) : Int :=
  width * height
```
Let's break down the syntax:
- **`def`**: The keyword to define a new function.
- **`area`**: The name of our function.
- **`(width : Int) (height : Int)`**: The arguments and their types.
- **`: Int :=`**: The final return type, followed by `:=` which means "is defined as".

Functions are written similar to "math" functions. Unlike Python or Java, there is no "return" keywords. Instead, everything on the right-hand side of the `:=` function is the return value.

To call a function in Lean, we use spaces. Instead of `area(2, 3)`, we write `area 2 3` or `(area 2 3)`.
For example, a function `cube_area` that calculates the surface area of a cube can be defined using calls to the area function above:
```lean
def cube_area (length : Int) : Int :=
  (area length length) * 6
```

> 🧠 **Check My Knowledge: Functions**
> 
> You are given two math functions that have the following signatures:
>  1. `def power (base : Int) (exponent : Int) : Int`
>  2. `def sqrt (n : Int) : Int`
>
> If you have a function `power` that takes a base and an exponent and a function `sqrt` that takes a number n, can you write a function called `hypotenuse` that takes two numbers `a` and `b`, squares them, and adds them together?
<details>
<summary>Answer</summary>

> ```lean
> def hypotenuse (a : Int) (b : Int) : Int :=
>   sqrt (add (power a 2) (power b 2))
> ```
</details>

### Concept: Pattern Matching & Tree Traversal
In functional programming, we process inductive types using **pattern matching**. Since our `Expr` can be either a `const` or a `binop`, we must define what happens in both cases.

If it's a `binop` (like `add e1 e2`), we need to evaluate the left branch (`e1`), evaluate the right branch (`e2`), and then add them together. Because `e1` and `e2` are also expressions, our function will call itself. This is **recursion**!

> 💡 **HINT: Pattern Matching Order**
> When you write pattern matching cases, **order matters!** Lean checks cases from top to bottom. If you have a wildcard `_` (catch-all) at the top, it will match everything and ignore the cases below it. Always put specific cases first, and general catch-all cases last.

> 📘 **LEAN SYNTAX: Lambdas and Dots**
> - **The Leading Dot:** In `| .add =>`, the dot means Lean is smart enough to know we mean `BinOp.add` without us typing the full name.
> - **Lambdas:** The symbol `(· + ·)` is a shortcut for an anonymous function (lambda): `fun x y => x + y`. It just means "a function that takes two things and adds them".

> 💻 **ACTION: Open `Semantics.lean`**
> 
> First, let's turn our abstract `BinOp` into actual math. 
> Define a function called `BinOp.denote`. It takes a `BinOp` and two `Int`s, and returns an `Int`.
> 
> **Skeleton:**
> ```lean
> def BinOp.denote : BinOp → Int → Int → Int
>   | .add => (· + ·)
>   | .sub => -- You do this one!
>   | .mul => -- And this one!
> ```

<details>
<summary>Answer</summary>
```lean
/-- Denotation of a binary operator as a function on integers. -/
def BinOp.denote : BinOp → Int → Int → Int
  | .add => (· + ·)
  | .sub => (· - ·)
  | .mul => (· * ·)
```
</details>

Now, let's write the source language evaluator.


> 📘 **LEAN SYNTAX: Dot Notation**
> In Python or Java, `object.method()` calls a method on an object. Lean has a similar trick. Writing `e₁.eval` is exactly the same as writing `Expr.eval e₁`. It's just syntax sugar to make it easier to read!

> 💻 **ACTION: Stay in `Semantics.lean`**
>
> Write `Expr.eval`. It takes an `Expr` and returns an `Int`.
>
> **Skeleton:**
> ```lean
> def Expr.eval : Expr → Int
>   | .const n => n
>   | .binop op e₁ e₂ => -- Use op.denote (with spaces for arguments!), and recursively call .eval on e₁ and e₂!
> ```

<details>
<summary>Answer</summary>

```lean
/-- The semantics of the source language: an interpreter mapping each
expression to the integer it denotes. -/
def Expr.eval : Expr → Int
  | .const n => n
  | .binop op e₁ e₂ => op.denote e₁.eval e₂.eval
```
</details>

## The Stack Evaluator

Now we need to write a function that executes a list of Stack Instructions (`Instr`). But we have a problem.

### Concept: The Option Type and Generics (Handling Errors)

What happens if our stack is empty, but the CPU receives an `add` instruction? It needs two numbers, but it has zero. In Java or Python, this might throw an `Exception` and crash the program.

Functional languages don't like sudden crashes. In Lean, functions **must** always return some value of their specified return type. There is no "throw Exception". So, how do we handle errors? We use the **Option** type.

The `Option` type is simply an inductive type built right into Lean. It allows us to say that a `none` *means* something went wrong. 

But what is an `Option` holding? An `Int`? A `String`? This introduces **Generics**. A generic type is a type that can hold *any* other type (represented by a placeholder like `α`).

Here is what the definition of `Option` looks like under the hood:
```lean
inductive Option (α : Type) where
  | none : Option α
  | some (val : α) : Option α
```
An `Option Int` can be one of two things:

1. `some 5` (We successfully got a number!)
2. `none` (Something went wrong, safely abort).

Notice that `some` is just a constructor that holds data (like our `const (n : Int)` from earlier). Because `Option` is an inductive type, we can **pattern match** on it! We can write one case for `| none => ...` to handle the error path, and one case for `| some val => ...` to handle the success path.

> 🧠 **Check My Thinking: Safe Execution**
>
> Look at these stack scenarios. Which ones return `some` stack, and which ones return `none`?
> 1. Stack: `[5]`, Instruction: `add`
> 2. Stack: `[3, 4]`, Instruction: `mul`

<details>
<summary>Answer</summary>

1. `none`. `add` requires two items, but we only have `[5]`. (Stack underflow!)
2. `some [12]`. `mul` pops 3 and 4, multiplies them, and pushes 12.
</details>

### Concept: Order of Operations on a Stack

Remember that a stack is Last-In, First-Out (LIFO).
If we want to compute `10 - 2`, we push `10`, then push `2`.
The stack looks like this: `[2, 10]`. (The `2` is on top!)
When we pop the top two items for a binary operation, the **first item we pop is the right operand**, and the **second item is the left operand**.

### Concept: Lists

A stack is just a list of items. Like `Option`, `List` is a generic inductive type in Lean! It can hold any type `α`. 
Here is what the definition of `List` roughly looks like:

```lean
inductive List (α : Type) where
  | nil : List α
  | cons (head : α) (tail : List α) : List α
```

A list is either empty (`nil`), or it is a single item (`head`) attached to another list (`tail`). 

If we have the list `[1, 2, 3]`, under the hood it is actually a chain of `cons` constructors pointing to each other, ending in `nil`:
```text
  cons(1) ---> cons(2) ---> cons(3) ---> nil
```

Lean has special syntax for lists to make this easier to read:
- `[]` is syntax for `nil` (the empty list).
- `[1, 2, 3]` creates a list with three items.
- `::` is syntax for the `cons` constructor. It attaches a head to a tail. So `1 :: [2, 3]` becomes `[1, 2, 3]`. We can also use `head :: tail` in pattern matching to split a list apart!

> 📘 **LEAN SYNTAX: Pattern Matching Tricks**
> - **abbrev:** `abbrev` is just a way to create a shortcut name for a type.
> - **Matching Multiple Things:** Notice the comma in `| [], stk =>`. This means we are pattern matching on *two* arguments at the same time: the instruction list, and the stack.
> - **Wildcards (`_`):** The underscore `_` means "I don't care what this value is, match anything".

> 💻 **ACTION: Open `Target.lean`**
>
> First, let's create a handy shortcut (alias) for our Stack type so we don't have to type `List Int` everywhere.
> ```lean
> abbrev Stack := List Int
> ```
> 
> Next, write the `exec` function. It takes a list of instructions, the current stack, and returns an `Option Stack`.
>
> **Skeleton:**
> ```lean
> def exec : List Instr → Stack → Option Stack
>   -- Case 1: No more instructions (`[]`). Return the final stack!
>   | [], stk => some stk
>   
>   -- Case 2: We have a `push` instruction followed by the rest of the program `p`.
>   -- We recursively call `exec` on `p`, adding `n` to the top of the stack (`n :: stk`).
>   | .push n :: p, stk => exec p (n :: stk)
>   
>   -- Case 3: We have a `binop` instruction. We need exactly two items on top of the stack.
>   -- Remember, the top item (`y`) is the right operand!
>   | .binop op :: p, y :: x :: stk => -- Call exec on p, using op.denote on x and y
>   
>   -- Case 4: A `binop` instruction, but we didn't match the case above (meaning < 2 items).
>   | .binop _ :: _, _ => none
> ```


<details>
<summary>Answer</summary>

```lean
/-- Run a program against a stack. -/
def exec : List Instr → Stack → Option Stack
  | [], stk => some stk
  | .push n :: p, stk => exec p (n :: stk)
  | .binop op :: p, y :: x :: stk => exec p (op.denote x y :: stk)
  | .binop _ :: _, _ => none

```

</details>


## Writing the Compiler!

You now have a working AST evaluator and a working Stack Machine. It's time to build the bridge.

### Concept: Compiling to RPN

Our `compile` function will take an `Expr` and return a `List Instr`.
Remember in Lesson 1? We turn an AST into Stack Instructions by doing a **post-order traversal** (Left Branch, Right Branch, Node).

If we have `add e1 e2`:

1. Compile `e1` (which pushes its result to the stack).
2. Compile `e2` (which pushes its result to the stack, right on top of `e1`'s result).
3. Add the `binop` instruction.

> 🤔 **Thinking Block**
>
> Why do we use `++` (List append) here instead of `::` (List cons)?

<details>
<summary>Answer</summary>

> Because compiling a sub-expression (`e1`) might result in *many* instructions, not just one. `++` joins two lists together, while `::` adds a single item to the front of a list. We want to glue the list of instructions from `e1` to the list of instructions from `e2`.
</details>


> 💻 **ACTION: Open `Compiler.lean`**
>
> This is it! The core of our software. Write the `Expr.compile` function.
>
> **Skeleton:**
> ```lean
> def Expr.compile : Expr → List Instr
>   | .const n => -- Return a list containing a single push instruction
>   | .binop op e₁ e₂ => -- Compile e1, append to compiled e2, append to a list with the binop
> ```



<details>
<summary>Answer</summary>

```lean
/-- Compile an expression to stack-machine code by post-order
traversal. -/
def Expr.compile : Expr → List Instr
  | .const n => [.push n]
  | .binop op e₁ e₂ => e₁.compile ++ e₂.compile ++ [.binop op]
```
</details>

### Running the Compiler

We have our compiler, but how do we get it to actually output anything? We need to glue everything together in a main file and print out the result. 

Because `compile` just returns a Lean `List Instr`, we need a helper function to translate those instructions into readable text and print them to standard output. 

> 💻 **ACTION: Open `Main.lean`**
>
> Copy and paste the following helper code into your `Main.lean` file. 
> Feel free to play around with `myProgram` and change the math expression to whatever you want!
>
> ```lean
> instance : ToString Instr where
>   toString
>     | .push n => s!"PUSH {n}"
>     | .binop .add => "ADD"
>     | .binop .sub => "SUB"
>     | .binop .mul => "MUL"
> 
> def serialize (is : List Instr) : String :=
>   String.intercalate "\n" (is.map toString)
> 
> def main : IO Unit := do
>   -- Example expression: (5 + 3) * 2
>   let myProgram := Expr.binop .mul (Expr.binop .add (Expr.const 5) (Expr.const 3)) (Expr.const 2)
>   let machineCode := myProgram.compile
>   let asmText := serialize machineCode
>   IO.println asmText
> ```
> 
> **To run this:** Open your terminal and run `lake exe verifiedcompiler`. You should see your compiler spit out the actual stack machine instructions!

### Wrap up

Take a step back and look at what you just built. You wrote a compiler!

If you give your compiler `(3 + 4) * 5`, it generates a list of stack instructions. If you feed those instructions into your `exec` machine, it will spit out `35`.

But how do we know it **always** works? Could there be a bug in our compiler where it messes up the order of operations for some massive, complicated AST?

In the next lesson, we transition from Software Engineers to Mathematicians. We aren't going to test our compiler; we are going to *prove* it is mathematically flawless.
