import Std
import Batteries.Data.Rat.Basic

open Std

/-- A simple expression language over rational numbers. -/
inductive Expr
  | const : Rat → Expr
  | var   : String → Expr             -- NEW: variable
  | add   : Expr → Expr → Expr
  | sub   : Expr → Expr → Expr
  | mul   : Expr → Expr → Expr
  | div   : Expr → Expr → Expr        -- safe division; fails on division by zero

namespace Expr

/-- Variable environment. -/
abbrev Env := Std.HashMap String Rat

/-- Evaluate an expression under an environment. -/
def evalWith : Expr → Env → Option Rat
  | const q, _      => some q
  | var name, env   => env.get? name
  | add a b, env    => return (← evalWith a env) + (← evalWith b env)
  | sub a b, env    => return (← evalWith a env) - (← evalWith b env)
  | mul a b, env    => return (← evalWith a env) * (← evalWith b env)
  | div a b, env    =>
      do
        let rb ← evalWith b env
        if rb = (0 : Rat) then none
        else
          let ra ← evalWith a env
          some (ra / rb)

/-- Partially evaluate an expression: substitute known variables and
    fold arithmetic when both sides become constants; leave unknown vars symbolic. -/
def partialEval : Expr → Env → Expr
  | const q, _ => const q
  | var name, env => match env.get? name with -- lookup the variable name, if in the environment, otherwise keep as it
    | some v => const v
    | none => var name

  /- for all binary methods nothing changes besides only doing the evaluation if two constants are present -/
  | add a b, env =>
      let a' := partialEval a env; let b' := partialEval b env;
      match a', b' with
      | const qa, const qb => const (qa + qb)
      | _, _ => add a' b'
  | sub a b, env =>
      let a' := partialEval a env; let b' := partialEval b env;
      match a', b' with
      | const qa, const qb => const (qa - qb)
      | _, _ => sub a' b'
  | mul a b, env =>
      let a' := partialEval a env; let b' := partialEval b env;
      match a', b' with
      | const qa, const qb => const (qa * qb)
      | _, _ => mul a' b'
  | div a b, env =>
      let a' := partialEval a env; let b' := partialEval b env;
      match a', b' with
      | const qa, const qb => if qb = (0 : Rat) then div a' b' else const (qa / qb)
      | _, _ => div a' b'

/-- Backward-compatible eval for closed expressions (no variables). -/
def eval (e : Expr) : Option Rat :=
  evalWith e ({} : Env)

/-- Helper smart constructors. -/
def mkAdd (a b : Rat) : Expr := add (const a) (const b)
def mkSub (a b : Rat) : Expr := sub (const a) (const b)
def mkMul (a b : Rat) : Expr := mul (const a) (const b)
def mkDiv (a b : Rat) : Expr := div (const a) (const b)
def mkVar (name : String) : Expr := var name    -- NEW

/-- Example: (1/2 + 3) * (4 / (5 - 5)) → division by zero => none. -/
def exampleBad : Expr :=
  mul
    (add (const (mkRat (1 : Int) (2:  Nat))) (const (3 : Rat)))
    (div (const (4 : Rat)) (sub (const (5 : Rat)) (const (5 : Rat))))

/-- Example: (1/2 + 3) * (4 / (5 - 2)) = (7/2) * (4 / 3) = 14/3. -/
def exampleGood : Expr :=
  mul
    (add (const (mkRat 1 2)) (const (3 : Rat)))
    (div (const (4 : Rat)) (sub (const (5 : Rat)) (const (2 : Rat))))

/-- Example with a variable: ((1/2) + x) * 2. -/
def exampleVar : Expr :=
  mul
    (add (const (mkRat 1 2)) (var "x"))
    (const (2 : Rat))

def envExample : Env := ({} : Env).insert "x" (3 : Rat)

def exampleVar2 : Expr :=
  add (add (const 1) (const 2)) (var "y")

#eval exampleBad.eval   -- none
#eval exampleGood.eval  -- some (Std.Rat.mk 14 3)
#eval exampleVar.evalWith envExample   -- some (Std.Rat.mk 7 1)
#eval exampleVar2.partialEval envExample

/-- Optional: pretty printing via toString. -/
def toString : Expr → String
  | const q    => s!"{q.num}/{q.den}"
  | var name   => name
  | add a b    => s!"({toString a} + {toString b})"
  | sub a b    => s!"({toString a} - {toString b})"
  | mul a b    => s!"({toString a} * {toString b})"
  | div a b    => s!"({toString a} / {toString b})"

def toStringOption: Option Rat → String
  | some x => s!"{x}"
  | none => s!"none"

instance : ToString Expr where
  toString := toString

instance : Repr Expr where
  reprPrec e _ := toString e

#eval toString exampleVar
#eval toString exampleGood
#eval toStringOption exampleBad.eval
#eval toString exampleVar
#eval toString (var "x")
#eval toStringOption (exampleVar.evalWith envExample)

end Expr
