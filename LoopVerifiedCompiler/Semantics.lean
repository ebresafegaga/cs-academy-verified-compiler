import LoopVerifiedCompiler.Source

namespace LoopVerifiedCompiler

/-- The program state: a value for every variable. -/
def State := String → Int

/-- The state with every variable set to `0`. -/
def State.init : State := fun _ => 0

/-- Update the value of one variable. -/
def State.update (st : State) (x : String) (v : Int) : State :=
  fun y => if y = x then v else st y

/-- Denotation of a binary operator as a function on integers. -/
def BinOp.denote : BinOp → Int → Int → Int
  | .add => (· + ·)
  | .sub => (· - ·)
  | .mul => (· * ·)

/-- Expression evaluation: total and pure, reading the state. -/
def Expr.eval (st : State) : Expr → Int
  | .const n => n
  | .var x => st x
  | .binop op e₁ e₂ => op.denote (e₁.eval st) (e₂.eval st)

/-- Big-step operational semantics of statements: `BigStep s st st'`
means running `s` from state `st` terminates in state `st'`.

This must be a relation rather than a function: `whileDo` can
diverge, and a diverging run is simply not related to any final
state. -/
inductive BigStep : Stmt → State → State → Prop where
  | skip {st : State} :
      BigStep .skip st st
  | assign {st : State} {x : String} {e : Expr} :
      BigStep (.assign x e) st (st.update x (e.eval st))
  | seq {s₁ s₂ : Stmt} {st st' st'' : State}
      (h₁ : BigStep s₁ st st') (h₂ : BigStep s₂ st' st'') :
      BigStep (.seq s₁ s₂) st st''
  | whileFalse {c : Expr} {body : Stmt} {st : State}
      (hc : c.eval st = 0) :
      BigStep (.whileDo c body) st st
  | whileTrue {c : Expr} {body : Stmt} {st st' st'' : State}
      (hc : c.eval st ≠ 0) (hbody : BigStep body st st')
      (hrest : BigStep (.whileDo c body) st' st'') :
      BigStep (.whileDo c body) st st''

end LoopVerifiedCompiler
