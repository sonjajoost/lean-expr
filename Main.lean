import Std
import Batteries.Data.Rat.Basic

open Std

/-- A simple expression language over rational numbers. -/
inductive Expr
  | const : Rat → Expr
  | add   : Expr → Expr → Expr
  | sub   : Expr → Expr → Expr
  | mul   : Expr → Expr → Expr
  | div   : Expr → Expr → Expr        -- safe division; fails on division by zero

namespace Expr

/-- Safely evaluate an expression. Returns `none` if a division by zero occurs. -/
def eval : Expr → Option Rat
  | const q   => some q
  | add a b   => return (← eval a) + (← eval b)
  | sub a b   => return (← eval a) - (← eval b)
  | mul a b   => return (← eval a) * (← eval b)
  | div a b   =>
      do
        let rb ← eval b
        if rb = (0 : Rat) then none
        else
          let ra ← eval a
          some (ra / rb)

/-- Helper smart constructors. -/
def mkAdd (a b : Rat) : Expr := add (const a) (const b)
def mkSub (a b : Rat) : Expr := sub (const a) (const b)
def mkMul (a b : Rat) : Expr := mul (const a) (const b)
def mkDiv (a b : Rat) : Expr := div (const a) (const b)

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

#eval exampleBad.eval   -- none
#eval exampleGood.eval  -- some (Std.Rat.mk 14 3)

/-- Optional: pretty printing via toString. -/
def toString : Expr → String
  | const q => s!"{q.num}/{q.den}"
  | add a b => s!"({toString a} + {toString b})"
  | sub a b => s!"({toString a} - {toString b})"
  | mul a b => s!"({toString a} * {toString b})"
  | div a b => s!"({toString a} / {toString b})"

def toStringOption: Option Rat → String
  | some x => s!"{x}"
  | none => s!"none"

instance : ToString Expr where
  toString := toString

instance : Repr Expr where
  reprPrec e _ := toString e

#eval toString exampleGood
#eval toStringOption exampleGood.eval

end Expr
