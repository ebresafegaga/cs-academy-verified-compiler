# Getting Started: Building a Certified Compiler

Welcome! In this self-guided tutorial, you are going to build a **Certified Compiler** from scratch. 

You won't just be writing code that translates math into machine instructions. You will be using mathematical logic to definitively *prove* that it is impossible for your compiler to ever make a mistake.

## What is Lean?

To accomplish this, we will be using **Lean**.

Lean is a purely functional programming language and a **theorem prover**. In most languages (like Python or Java), you write code and then write unit tests hoping to catch bugs. In Lean, the language itself understands mathematical logic. You can write "Theorems" about your code, and Lean will verify if your proofs are mathematically sound. If your proof has a flaw, the code simply won't compile!

Lean is increasingly being used by mathematicians to formalize complex math (like verifying Fermat's Last Theorem) and by software engineers to build ultra-secure, bug-free software.

### Installation

Before you begin, you'll need to install Lean on your computer. It comes with a great VS Code extension that will give you interactive feedback as you write your code and proofs.

> 🛠️ **Install Lean Here:** [https://lean-lang.org/install/](https://lean-lang.org/install/)

---

## Course Overview

This tutorial is broken down into three core lessons:

### [Lesson 1: Foundations & Functional Thinking](1_foundations.md)
You will learn how computers read math using Abstract Syntax Trees (ASTs), and how simple CPUs execute instructions using a Stack Machine. You will then define the foundational data structures for your compiler using Lean's `inductive` types.

### [Lesson 2: Evaluators & The Compiler](2_compiler.md)
You will bring your data structures to life. You'll write an **Evaluator** that calculates the mathematical answer to an expression, and a **Simulator** that runs instructions on a stack. Finally, you will write the **Compiler** itself: a function that translates your AST into a list of machine instructions.

### [Lesson 3: Certification & Proofs](3_proving.md)
You will transition from a Software Engineer to a Mathematician. You will learn the basics of Lean's Tactic Mode to write a mathematical proof guaranteeing that your Evaluator's answer perfectly matches the result of your compiled Stack instructions, for *every possible program in the universe*.
