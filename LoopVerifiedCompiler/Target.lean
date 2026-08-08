import LoopVerifiedCompiler.Semantics

namespace LoopVerifiedCompiler

/-- Instructions of the stack machine. New over the conditional
extension: `load`/`store` for variables, and a backward jump.
`jz k` pops the stack top and skips the next `k` instructions if it
is zero; `jmpBack k` continues `k` instructions before the following
one (new pc = pc + 1 - k), which is what loops need to jump back to
their condition. -/
inductive Instr where
  | push (n : Int)
  | load (x : String)
  | store (x : String)
  | binop (op : BinOp)
  | jz (k : Nat)
  | jmpBack (k : Nat)
  deriving Repr, DecidableEq

/-- The machine's operand stack. -/
abbrev Stack := List Int

/-- A machine configuration: program counter, operand stack, state. -/
abbrev Config := Nat × Stack × State

/-- One step of the machine running program `P`. Because jumps can go
backward, execution can no longer discard instructions as it goes: a
configuration keeps a program counter into the full program. A stuck
configuration (pc outside the program, stack underflow) simply has no
successor. -/
inductive Step (P : List Instr) : Config → Config → Prop where
  | push (h : P[pc]? = some (.push n)) :
      Step P (pc, stk, st) (pc + 1, n :: stk, st)
  | load (h : P[pc]? = some (.load x)) :
      Step P (pc, stk, st) (pc + 1, st x :: stk, st)
  | store (h : P[pc]? = some (.store x)) :
      Step P (pc, v :: stk, st) (pc + 1, stk, st.update x v)
  | binop (h : P[pc]? = some (.binop op)) :
      Step P (pc, y :: x :: stk, st) (pc + 1, op.denote x y :: stk, st)
  | jzTaken (h : P[pc]? = some (.jz k)) :
      Step P (pc, 0 :: stk, st) (pc + 1 + k, stk, st)
  | jzNotTaken (h : P[pc]? = some (.jz k)) (hv : v ≠ 0) :
      Step P (pc, v :: stk, st) (pc + 1, stk, st)
  | jmpBack (h : P[pc]? = some (.jmpBack k)) :
      Step P (pc, stk, st) (pc + 1 - k, stk, st)

/-- Zero or more machine steps. -/
inductive Steps (P : List Instr) : Config → Config → Prop where
  | refl : Steps P c c
  | head (h : Step P c₁ c₂) (t : Steps P c₂ c₃) : Steps P c₁ c₃

theorem Steps.single (h : Step P c₁ c₂) : Steps P c₁ c₂ :=
  .head h .refl

theorem Steps.trans (h₁ : Steps P c₁ c₂) : Steps P c₂ c₃ → Steps P c₁ c₃ := by
  induction h₁ with
  | refl => exact fun h₂ => h₂
  | head hs _ ih => exact fun h₂ => .head hs (ih h₂)

/-- Executable mirror of `Step`, used to demo compiled programs.
Correctness is stated against the `Step`/`Steps` relations. -/
def step (P : List Instr) : Config → Option Config
  | (pc, stk, st) =>
    match P[pc]?, stk with
    | some (.push n), stk => some (pc + 1, n :: stk, st)
    | some (.load x), stk => some (pc + 1, st x :: stk, st)
    | some (.store x), v :: stk => some (pc + 1, stk, st.update x v)
    | some (.binop op), y :: x :: stk => some (pc + 1, op.denote x y :: stk, st)
    | some (.jz k), v :: stk => some (if v = 0 then pc + 1 + k else pc + 1, stk, st)
    | some (.jmpBack k), stk => some (pc + 1 - k, stk, st)
    | _, _ => none

/-- Run the machine for at most `fuel` steps, stopping when the pc
reaches the end of the program. -/
def run (P : List Instr) : Nat → Config → Option Config
  | 0, _ => none
  | fuel + 1, c =>
    if c.1 = P.length then some c
    else match step P c with
      | some c' => run P fuel c'
      | none => none

end LoopVerifiedCompiler
