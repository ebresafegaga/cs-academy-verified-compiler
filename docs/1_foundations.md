# Lesson 1: Foundations & Functional Thinking

In this lesson, we are going to learn how computers actually read math, how a basic CPU processes instructions, and how to start modeling these concepts in a functional programming language called Lean.

By the end of this lesson, you will have written the foundational data structures for your very own compiler.

## The Problem & The Hardware

### Concept: The Abstract Syntax Tree (AST)

When you read the math expression `(3 + 4) * 5`, you use BEDMAS/PEMDAS to know that the addition happens first. But a computer doesn't read left-to-right like we do. Instead, it parses code into an **Abstract Syntax Tree (AST)**. "Syntax" just refers to the symbols and rules of a language.

An AST breaks operations down into a tree structure composed of **nodes**. The "leaves" (bottom nodes) are numbers, and the "branches" (inner nodes) are operators. 

For `(3 + 4) * 5`, the AST looks like this:
```text
      *
     / \
    +   5
   / \
  3   4
```

> 🧠 **Check My Thinking: ASTs**
>
> Try drawing the AST for the expression: `(10 - 2) * (4 + 1)`

<details>
<summary>Answer</summary>

> ```text
>       *
>      / \
>     -   +
>    / \ / \
>  10  2 4  1
> ```
</details>

### Concept: The Stack Machine

Most modern languages eventually boil down to simple instructions for the hardware, known as machine code. Every physical CPU has its own specific machine code it understands. For the purposes of our project, we are going to use a **Stack Machine** as our target hardware. Imagine a basic CPU that has no variables and no complex memory. It only has a **Stack**.

A stack is a **LIFO (Last-In, First-Out)** data structure. Think of it like a stack of plates in a cafeteria: you can only add a plate to the top (Push), and you can only take a plate off the top (Pop).

```text
  Push(5)       Push(8)        Pop() -> 8
   |              |               ^
   v              v               |
 [   ]          [ 8 ]           [   ]
 [ 5 ]          [ 5 ]           [ 5 ]
  ---            ---             ---
```

Our stack machine only has two types of instructions:

1. `push(n)`: Puts the number `n` on top of the stack.
2. `binop(op)`: "binop" stands for **binary operation**. Operations like `+`, `-`, and `*` are binary operations because they take exactly two items. This instruction pops the top two numbers, applies the operation, and pushes the result back onto the stack. Think of `binop` as a four-step dance: **Pop, Pop, Op, Push**.

```text
  binop(add) executing on a Stack:
  
  [ 4 ]  --Pop(4)-->  [   ]  --Pop(3)-->  [   ]       [   ]
  [ 3 ]               [ 3 ]               [   ]       [   ]
  [ 5 ]               [ 5 ]               [ 5 ]       [ 7 ] <- Push(4+3)
   ---                 ---                 ---         ---
```

### Concept: Reverse Polish Notation (RPN)

If we only have a stack, how do we write the math equation `(3 + 4) * 5`? We use **Reverse Polish Notation (RPN)**. RPN writes the numbers first, followed by the operator.

To turn an AST into RPN, we do a "post-order traversal": read the left branch, read the right branch, then read the node. This perfectly preserves the order of operations without needing parentheses!

For example:
- `3 + 4` becomes `3 4 +`.
- `2 + 3 * 4` (multiply first) becomes `2 3 4 * +`.
- `(2 + 3) * 4` (add first) becomes `2 3 + 4 *`.
- `(3 + 4) * 5` becomes `3 4 + 5 *`.

Why are we learning this? Because RPN translates directly into the instructions our stack machine can understand! Writing RPN is exactly the same as writing machine code for a stack-based CPU.

> 🧠 **Check My Thinking: Stack Execution**
>
> Let's act like the CPU! Run the RPN instructions `3 4 + 5 *` on an empty stack. What happens at each step?
<details>
<summary>Answer</summary>

> 1. `push 3` -> Stack: `[3]`
> 2. `push 4` -> Stack: `[4, 3]` *(4 is on top!)*
> 3. `add`    -> Pop 4 and 3, add them (7), push 7 -> Stack: `[7]`
> 4. `push 5` -> Stack: `[5, 7]`
> 5. `mul`    -> Pop 5 and 7, multiply them (35), push 35 -> Stack: `[35]`
> 
> 
> **Final Answer:** 35

</details>


## Hello, Lean

We are going to write our compiler in **Lean**, a purely functional programming language and theorem prover.

### Concept: Functional vs. Imperative

If you've used Python or Java (imperative languages), you are used to variables that change:

```python
x = 5
x = x + 1 # x is now 6

```

In Lean (a functional language), **state does not change**. There are no `while` loops, and variables cannot be mutated. Once `x` is 5, it is 5 forever. We compute things by passing data through functions, creating *new* data along the way.

> 🤔 **Thinking Block**
>
> Why might it be useful to have a programming language where data can never change once it's created?

<details>
<summary>Answer</summary>

> If variables can change at any time (especially in complex, multi-threaded programs), it's incredibly hard to guarantee that a program is bug-free. By making data immutable, we can treat our code like mathematical equations. This makes it possible to mathematically *prove* our code is correct!

</details>

### Concept: Inductive Types

To build our AST and Stack, we need a way to define custom data types. In Lean, we use `inductive` types. If you're coming from Python or Java, you can think of them a bit like enums or subclasses, but more powerful. They define all the possible "shapes" or "variants" a piece of data can take.

For example, a `TrafficLight` type can take three shapes:

```lean
inductive TrafficLight where
  | red
  | yellow
  | green
```
Here, `red`, `yellow`, and `green` are called the **constructors** of the `TrafficLight` type. The idea is that a `TrafficLight` is *only* one of these three options—it can never be anything else.

Lean uses inductive types heavily. A very common pattern you will see later is writing functions using **pattern matching**. We write code that works like a `switch` or `cases` statement, going one by one for each inductive shape, defining what happens if the light is red, what happens if it's yellow, etc.

> 📘 **LEAN SYNTAX: deriving**
> You'll often see `deriving Repr, DecidableEq` at the end of a type. This automatically teaches Lean how to print (`Repr`) and compare (`DecidableEq`) the type so we don't have to write that code manually!

### Concept: Constructors Holding Data

Constructors don't have to just be empty labels like `red` or `green`. In Lean, **constructors can hold data**. 

Why is this important? Imagine a `Shape` inductive type. A `circle` needs to store a radius (a number). A `rectangle` needs to store a width and height.

```lean
inductive Shape where
  | circle (radius : Float)
  | rectangle (width : Float) (height : Float)
```
This is how we represent complex data in Lean. A `Shape` isn't just one of two variants; it also carries around the necessary data for whichever variant it is. Keep this in mind when we build our AST!

## Modeling our Compiler with Inductive

It's time to write some code! Open your project folder. We'll be working in the `Source.lean` and `Target.lean` files.

### Defining Source Operations

First, we need to define the mathematical operations our source language supports: addition, subtraction, and multiplication.

> 💻 **ACTION: Open `Source.lean`**.
>
> Create an inductive type called `BinOp`. It should have three cases: `add`, `sub`, and `mul`.
>
> *(Hint: copy the structure of the TrafficLight example above!)*
>
> Add `deriving Repr, DecidableEq` at the end so Lean knows how to print and compare these operations.

<details>
<summary>Answer</summary>

```lean
/-- Binary operators of the source language. -/
inductive BinOp where
  | add
  | sub
  | mul
  deriving Repr, DecidableEq
```

> 📘 **LEAN SYNTAX: Docstrings**
> Notice the `/-- ... -/` above the code? That is a documentation comment (docstring) in Lean, similar to `"""` in Python or `/** ... */` in Java.
</details>

### Defining the Abstract Syntax Tree

Now we need to define our AST nodes. We'll call this type `Expr` (short for Expression).
An expression can be one of two things:

1. A constant integer (like `5`).
2. A binary operation, which consists of an operator (a `BinOp`) and a left and right branch (which are both themselves `Expr`s).

> 📘 **LEAN SYNTAX: Shorthand Arguments**
> Remember that constructors can hold data, so `| const (n : Int)` carries an integer.
> Also, a handy shortcut: `(e₁ e₂ : Expr)` is Lean shorthand for `(e₁ : Expr) (e₂ : Expr)`.

> 💻 **ACTION: Stay in `Source.lean`**
>
> Try to define the `Expr` inductive type.
>
> **Skeleton:**
> ```lean
> inductive Expr where
>   | const (n : Int)
>   | binop ... -- You fill this in! (needs an op, and two Exprs e₁ e₂)
>   deriving Repr, DecidableEq
> ```


<details>
<summary>Answer</summary>

```lean
/-- Abstract syntax of source expressions: integer constants and
binary operations. -/
inductive Expr where
  | const (n : Int)
  | binop (op : BinOp) (e₁ e₂ : Expr)
  deriving Repr, DecidableEq

```
*(Note: To type the subscript numbers like `e₁`, you can type `e\1` in your Lean editor!)*

</details>


### Defining the Target Stack Machine

We have our Source (the AST). Now we need our Target (the Stack machine).

Our stack machine needs a list of instructions to execute. Let's define what a single instruction looks like. Remember, our machine can only push a number, or perform a binary operation on the top two numbers.

> 💻 **ACTION: Open `Target.lean`**
>
> Define an inductive type called `Instr` (short for Instruction).
> It should have two constructors:
> 1. `push` which takes an `Int`.
> 2. `binop` which takes a `BinOp`.

<details>
<summary>Answer</summary>

```lean
/-- Instructions of the stack machine. -/
inductive Instr where
  | push (n : Int)
  | binop (op : BinOp)
  deriving Repr, DecidableEq
```
</details>

### Wrap up

Congratulations! You have successfully built the underlying data architecture for your compiler.

You've defined the `Source` language (`Expr`) and the `Target` language (`Instr`). In the next lesson, we will write the actual compiler function that translates an `Expr` into a list of `Instr`s!

