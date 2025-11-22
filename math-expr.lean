import Std.Tactic
import Batteries.Data.Rat.Basic

/-- Expressions with variables. -/
inductive Expr
  | const : Rat → Expr
  | var   : String → Expr
  | add   : Expr → Expr → Expr
  | sub   : Expr → Expr → Expr
  | mul   : Expr → Expr → Expr
  | div   : Expr → Expr → Expr
open Expr

abbrev Env := Std.HashMap String Rat

/-- Evaluation with environment (returns none for div by zero or missing variable). -/
def eval : Expr → Env → Option Rat
  | const q, _ => some q
  | var name, env => env[name]?
  | add a b, env => do (← eval a env) + (← eval b env) -- returns none if one sub-evaluation is none
  | sub a b, env => do (← eval a env) - (← eval b env)
  | mul a b, env => do (← eval a env) * (← eval b env)
  | div a b, env => do
      let rb ← eval b env
      if rb = (0 : Rat) then none
      else
        let ra ← eval a env
        pure (ra / rb)

/-- Values are just constants. -/
inductive Value : Expr → Prop
  | constv (q : Rat) : Value (const q)
open Value

/-- Environment-aware small-step relation. -/
inductive Step (env : Env) : Expr → Expr → Prop
| varV {name q} : env.get? name = some q → Step env (var name) (const q)
| addL {e1 e1' e2} : Step env e1 e1' → Step env (add e1 e2) (add e1' e2)
| addR {v e2 e2'} : Value v → Step env e2 e2' → Step env (add v e2) (add v e2')
| addV {q1 q2} : Step env (add (const q1) (const q2)) (const (q1 + q2))
| subL {e1 e1' e2} : Step env e1 e1' → Step env (sub e1 e2) (sub e1' e2)
| subR {v e2 e2'} : Value v → Step env e2 e2' → Step env (sub v e2) (sub v e2')
| subV {q1 q2} : Step env (sub (const q1) (const q2)) (const (q1 - q2))
| mulL {e1 e1' e2} : Step env e1 e1' → Step env (mul e1 e2) (mul e1' e2)
| mulR {v e2 e2'} : Value v → Step env e2 e2' → Step env (mul v e2) (mul v e2')
| mulV {q1 q2} : Step env (mul (const q1) (const q2)) (const (q1 * q2))
| divL {e1 e1' e2} : Step env e1 e1' → Step env (div e1 e2) (div e1' e2)
| divR {v e2 e2'} : Value v → Step env e2 e2' → Step env (div v e2) (div v e2')
| divV {q1 q2} : q2 ≠ 0 → Step env (div (const q1) (const q2)) (const (q1 / q2))
open Step

/-- Multi-step closure. -/
inductive Steps (env : Env) : Expr → Expr → Prop
| refl {e} : Steps env e e
| trans {e e' e''} : Steps env e e' → Step env e' e'' → Steps env e e''
open Steps

theorem Steps.append {env a b c} : Steps env a b → Steps env b c → Steps env a c := by
  intro h1 h2; induction h2 with
  | refl => simpa using h1
  | trans hpre st ih => exact Steps.trans ih st

theorem Steps.congrCtx {env} (C : Expr → Expr)
    (hC : ∀ {x y}, Step env x y → Step env (C x) (C y)) : ∀ {x y}, Steps env x y → Steps env (C x) (C y) := by
  intro x y h; induction h with
  | refl => exact Steps.refl
  | trans hpre st ih => exact Steps.trans ih (hC st)

theorem Steps.liftCtx {env} (C : Expr → Expr)
    (hC : ∀ {x y}, Step env x y → Step env (C x) (C y)) {x y} : Steps env x y → Steps env (C x) (C y) :=
  Steps.congrCtx C hC

theorem Steps.reduceAdd {env e1 e2 r1 r2}
    (s1 : Steps env e1 (const r1)) (s2 : Steps env e2 (const r2)) :
    Steps env (add e1 e2) (const (r1 + r2)) := by
  have L := Steps.liftCtx (env:=env) (fun t => add t e2) (fun s => Step.addL s) s1
  have R := Steps.liftCtx (env:=env) (fun t => add (const r1) t) (fun s => Step.addR (Value.constv r1) s) s2
  exact Steps.trans (Steps.append L R) Step.addV

theorem Steps.reduceSub {env e1 e2 r1 r2}
    (s1 : Steps env e1 (const r1)) (s2 : Steps env e2 (const r2)) :
    Steps env (sub e1 e2) (const (r1 - r2)) := by
  have L := Steps.liftCtx (env:=env) (fun t => sub t e2) (fun s => Step.subL s) s1
  have R := Steps.liftCtx (env:=env) (fun t => sub (const r1) t) (fun s => Step.subR (Value.constv r1) s) s2
  exact Steps.trans (Steps.append L R) Step.subV

theorem Steps.reduceMul {env e1 e2 r1 r2}
    (s1 : Steps env e1 (const r1)) (s2 : Steps env e2 (const r2)) :
    Steps env (mul e1 e2) (const (r1 * r2)) := by
  have L := Steps.liftCtx (env:=env) (fun t => mul t e2) (fun s => Step.mulL s) s1
  have R := Steps.liftCtx (env:=env) (fun t => mul (const r1) t) (fun s => Step.mulR (Value.constv r1) s) s2
  exact Steps.trans (Steps.append L R) Step.mulV

theorem Steps.reduceDiv {env e1 e2 r1 r2}
    (nz : r2 ≠ 0)
    (s1 : Steps env e1 (const r1)) (s2 : Steps env e2 (const r2)) :
    Steps env (div e1 e2) (const (r1 / r2)) := by
  have L := Steps.liftCtx (env:=env) (fun t => div t e2) (fun s => Step.divL s) s1
  have R := Steps.liftCtx (env:=env) (fun t => div (const r1) t) (fun s => Step.divR (Value.constv r1) s) s2
  exact Steps.trans (Steps.append L R) (Step.divV nz)

/-- Single-step preserves evaluation. -/
theorem step_preserves_eval {e e' env} : Step env e e' → eval e env = eval e' env := by
  intro s; induction s <;> simpa [eval, *] -- ignore warning
  -- long form
  /-
  expose_names
  induction s with
  | varV hv => simpa [eval] using hv
  | addL _ ih => simp [eval, ih]
  | addR _ _ ih => simp [eval, ih]
  | addV => simp [eval]
  | subL _ ih => simp [eval, ih]
  | subR _ _ ih => simp [eval, ih]
  | subV => simp [eval]
  | mulL _ ih => simp [eval, ih]
  | mulR _ _ ih => simp [eval, ih]
  | mulV => simp [eval]
  | divL _ ih => simp [eval, ih]
  | divR _ _ ih => simp [eval, ih]
  | divV nz => simp [eval, nz]
  -/

/-- Multi-step preserves evaluation. -/
theorem steps_preserve_eval {e e' env} : Steps env e e' → eval e env = eval e' env := by
  intro h; induction h with
  | refl => simp
  | trans h1 h2 ih => rw [ih, step_preserves_eval h2]

/-- Soundness: reaching a constant implies eval gives that constant. -/
theorem small_step_soundness {e q env} : Steps env e (const q) → eval e env = some q := by
  intro h; have : eval e env = eval (const q) env := steps_preserve_eval h; simpa [eval] using this

/-- Completeness: evaluation result implies multi-step to same constant. -/
theorem eval_some_implies_steps_to_const {e q env} : eval e env = some q → Steps env e (const q) := by
  revert q
  induction e with
  | const r =>
      intro q h; simp [eval] at h; rw[h]; exact Steps.refl
  | var name =>
      intro q h
      have hv : env.get? name = some q := by simpa [eval] using h
      exact Steps.trans Steps.refl (Step.varV hv)
  | add e1 e2 ih1 ih2 =>
      intro q h
      cases he1 : eval e1 env with
      | none => simp [eval, he1] at h
      | some r1 =>
        cases he2 : eval e2 env with
        | none => simp [eval, he1, he2] at h
        | some r2 =>
          have : some (r1 + r2) = some q := by simpa [eval, he1, he2] using h
          cases this
          have s1 : Steps env e1 (const r1) := ih1 (q := r1) he1
          have s2 : Steps env e2 (const r2) := ih2 (q := r2) he2
          exact Steps.reduceAdd s1 s2
  | sub e1 e2 ih1 ih2 =>
      intro q h
      cases he1 : eval e1 env with
      | none => simp [eval, he1] at h
      | some r1 =>
        cases he2 : eval e2 env with
        | none => simp [eval, he1, he2] at h
        | some r2 =>
          have : some (r1 - r2) = some q := by simpa [eval, he1, he2] using h
          cases this
          have s1 : Steps env e1 (const r1) := ih1 (q := r1) he1
          have s2 : Steps env e2 (const r2) := ih2 (q := r2) he2
          exact Steps.reduceSub s1 s2
  | mul e1 e2 ih1 ih2 =>
      intro q h
      cases he1 : eval e1 env with
      | none => simp [eval, he1] at h
      | some r1 =>
        cases he2 : eval e2 env with
        | none => simp [eval, he1, he2] at h
        | some r2 =>
          have : some (r1 * r2) = some q := by simpa [eval, he1, he2] using h
          cases this
          have s1 : Steps env e1 (const r1) := ih1 (q := r1) he1
          have s2 : Steps env e2 (const r2) := ih2 (q := r2) he2
          exact Steps.reduceMul s1 s2
  | div e1 e2 ih1 ih2 =>
      intro q h
      cases he2 : eval e2 env with
      | none => simp [eval, he2] at h
      | some r2 =>
        cases he1 : eval e1 env with
        | none => simp [eval, he1, he2] at h
        | some r1 =>
          have nz : r2 ≠ 0 := by intro z; simp [eval, he1, he2, z] at h
          have : some (r1 / r2) = some q := by simpa [eval, he1, he2, nz] using h
          cases this
          have s1 : Steps env e1 (const r1) := ih1 (q := r1) he1
          have s2 : Steps env e2 (const r2) := ih2 (q := r2) he2
          exact Steps.reduceDiv nz s1 s2

/-- An expression is stuck if it cannot step further. -/
def Stuck (env : Env) (e : Expr) : Prop := ¬∃ e', Step env e e'

/-- If we reach a stuck non-value, eval must be none. -/
theorem stuck_implies_eval_none {e env} (hstuck : Stuck env e) (hnval : ¬Value e) : eval e env = none := by
  sorry
/-- If eval returns none, expression steps to a stuck state. -/
theorem eval_none_implies_steps_to_stuck {e env} (h : eval e env = none) :
    ∃ e', Steps env e e' ∧ Stuck env e' ∧ ¬Value e' := by
  sorry

/-- Main theorem: eval returns none iff expression steps to a stuck state. -/
theorem eval_none_iff_steps_to_stuck {e env} :
    eval e env = none ↔ ∃ e', Steps env e e' ∧ Stuck env e' ∧ ¬Value e' := by
  constructor
  · exact eval_none_implies_steps_to_stuck
  · intro ⟨e', hs, hstuck, hnval⟩
    have : eval e env = eval e' env := steps_preserve_eval hs
    rw [this]
    exact stuck_implies_eval_none hstuck hnval


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
#eval eval exampleBad envExample  -- none
#eval eval exampleGood envExample  -- some (Std.Rat.mk 14 3)

def myToString : Expr → String
  | const q    => s!"{q.num}/{q.den}"
  | var name   => name
  | add a b    => s!"({myToString a} + {myToString b})"
  | sub a b    => s!"({myToString a} - {myToString b})"
  | mul a b    => s!"({myToString a} * {myToString b})"
  | div a b    => s!"({myToString a} / {myToString b})"

def toStringOption: Option Rat → String
  | some x => s!"{x}"
  | none => s!"none"

instance : ToString Expr where
  toString := myToString

instance : Repr Expr where
  reprPrec e _ := myToString e

#eval toString exampleVar
#eval toString exampleGood
#eval toStringOption (eval exampleBad envExample)
#eval toString exampleVar
#eval toString (var "x")
#eval toStringOption (eval exampleVar envExample)
