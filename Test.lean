import Std.Tactic -- optional, for convenience
import Batteries.Data.Rat.Basic

/-- The expression datatype you gave -/
inductive Expr
  | const : Rat → Expr
  | add   : Expr → Expr → Expr
  | sub   : Expr → Expr → Expr
  | mul   : Expr → Expr → Expr
  | div   : Expr → Expr → Expr
-- negative?

open Expr

/-- safe evaluation returning `none` on division by zero -/
def eval : Expr → Option Rat
  | const q   => some q
  | add a b   => do (← eval a) + (← eval b)
  | sub a b   => do (← eval a) - (← eval b)
  | mul a b   => do (← eval a) * (← eval b)
  | div a b   =>
    do
      let rb ← eval b
      if rb = (0 : Rat) then none
      else
        let ra ← eval a
        some (ra / rb)

/-- Values = only constants -/
inductive Value : Expr → Prop
  | constv (q : Rat) : Value (const q)

open Value

/-- single small-step relation matching your rules -/
inductive Step : Expr → Expr → Prop
| addL  {e1 e1' e2} : Step e1 e1' → Step (add e1 e2) (add e1' e2)
| addR  {v e2 e2'}  : Value v → Step e2 e2' → Step (add v e2) (add v e2')
| addV  {q1 q2}     : Step (add (const q1) (const q2)) (const (q1 + q2))

| subL  {e1 e1' e2} : Step e1 e1' → Step (sub e1 e2) (sub e1' e2)
| subR  {v e2 e2'}  : Value v → Step e2 e2' → Step (sub v e2) (sub v e2')
| subV  {q1 q2}     : Step (sub (const q1) (const q2)) (const (q1 - q2))

| mulL  {e1 e1' e2} : Step e1 e1' → Step (mul e1 e2) (mul e1' e2)
| mulR  {v e2 e2'}  : Value v → Step e2 e2' → Step (mul v e2) (mul v e2')
| mulV  {q1 q2}     : Step (mul (const q1) (const q2)) (const (q1 * q2))

| divL  {e1 e1' e2} : Step e1 e1' → Step (div e1 e2) (div e1' e2)
| divR  {v e2 e2'}  : Value v → Step e2 e2' → Step (div v e2) (div v e2')
| divV  {q1 q2}     : q2 ≠ 0 → Step (div (const q1) (const q2)) (const (q1 / q2))

open Step

/-- Many-step (reflexive-transitive) closure -/
inductive Steps : Expr → Expr → Prop
| refl {e} : Steps e e
| trans {e e' e''} : Steps e e' → Step e' e'' → Steps e e''

open Steps

/-! ### Single-step preserves evaluation - -/

theorem step_preserves_eval {e e'} : Step e e' → eval e = eval e' := by
intro s; induction s <;> simp [eval, *] -- apply simp [eval, induction hypothesis] to all subgoals

/-! ### Multi-step preserves evaluation - -/

theorem steps_preserve_eval {e e'} : Steps e e' → eval e = eval e' := by
  intro h
  induction h with
  | refl => simp
  | trans h1 h2 ih => rw [ih, step_preserves_eval h2]

/-! ### Soundness: if e →* const q then eval e = some q - -/

theorem small_step_soundness {e q} : Steps e (const q) → eval e = some q := by
  intro h
  have : eval e = eval (const q) := steps_preserve_eval h
  simp [eval] at this
  exact this

/-
  Optional: completeness (the other direction).
  If `eval e = some q` then `e →* const q`. This is provable by induction on the structure of `e` / the
  `eval` computation, using the congruence rules and the value computation rules.
-/

theorem eval_some_implies_steps_to_const {e q} :
  eval e = some q → Steps e (const q) := by
  -- helper: compose two multi-step derivations
  have append : ∀ {a b c}, Steps a b → Steps b c → Steps a c := by
    intro a b c h1 h2
    induction h2 with
    | refl => simpa using h1
    | trans hpre st ih => exact Steps.trans ih st
  -- helper: lift multi-steps through a unary context given a congruence step
  have liftCtx : ∀ (C : Expr → Expr), (∀ {x y}, Step x y → Step (C x) (C y)) → ∀ {x y}, Steps x y → Steps (C x) (C y) := by
    intro C ctx x y hxy
    induction hxy with
    | refl => exact Steps.refl
    | trans hpre st ih => exact Steps.trans ih (ctx st)
  revert q
  induction e with
  | const r =>
      intro q h
      -- from some r = some q we rewrite q to r and finish by refl
      have hs : some r = some q := by unfold eval at h; exact h
      cases hs
      exact Steps.refl
  | add e1 e2 ih1 ih2 =>
      intro q h
      cases he1 : eval e1 with
        | none => /- exfalso; -/ simp [eval, he1] at h
        | some r1 =>
          cases he2 : eval e2 with
            | none => simp [eval, he1, he2] at h
            | some r2 =>
              have hsum : some (r1 + r2) = some q := by simpa [eval, he1, he2] using h
              -- rewrite q to r1+r2
              cases hsum
              have s1 : Steps e1 (const r1) := ih1 (q := r1) he1
              have s2 : Steps e2 (const r2) := ih2 (q := r2) he2
              -- lift s1
              have liftLeft : Steps (add e1 e2) (add (const r1) e2) :=
                (liftCtx (fun t => add t e2) (fun s => Step.addL s)) s1
              -- lift s2
              have liftRight : Steps (add (const r1) e2) (add (const r1) (const r2)) :=
                (liftCtx (fun t => add (const r1) t) (fun s => Step.addR (Value.constv r1) s)) s2
              have final : Step (add (const r1) (const r2)) (const (r1 + r2)) := Step.addV
              have both : Steps (add e1 e2) (add (const r1) (const r2)) := append liftLeft liftRight
              exact Steps.trans both final
  | sub e1 e2 ih1 ih2 =>
      intro q h
      cases he1 : eval e1 with
        | none => simp [eval, he1] at h
        | some r1 =>
          cases he2 : eval e2 with
            | none => simp [eval, he1, he2] at h
            | some r2 =>
              have hsub : some (r1 - r2) = some q := by simpa [eval, he1, he2] using h
              cases hsub
              have s1 : Steps e1 (const r1) := ih1 (q := r1) he1
              have s2 : Steps e2 (const r2) := ih2 (q := r2) he2
              have liftLeft : Steps (sub e1 e2) (sub (const r1) e2) :=
                (liftCtx (fun t => sub t e2) (fun s => Step.subL s)) s1
              have liftRight : Steps (sub (const r1) e2) (sub (const r1) (const r2)) :=
                (liftCtx (fun t => sub (const r1) t) (fun s => Step.subR (Value.constv r1) s)) s2
              have final : Step (sub (const r1) (const r2)) (const (r1 - r2)) := Step.subV
              have both : Steps (sub e1 e2) (sub (const r1) (const r2)) := append liftLeft liftRight
              exact Steps.trans both final
  | mul e1 e2 ih1 ih2 =>
      intro q h
      cases he1 : eval e1 with
        | none =>  simp [eval, he1] at h
        | some r1 =>
          cases he2 : eval e2 with
            | none => simp [eval, he1, he2] at h
            | some r2 =>
              have hmul : some (r1 * r2) = some q := by simpa [eval, he1, he2] using h
              cases hmul
              have s1 : Steps e1 (const r1) := ih1 (q := r1) he1
              have s2 : Steps e2 (const r2) := ih2 (q := r2) he2
              have liftLeft : Steps (mul e1 e2) (mul (const r1) e2) :=
                (liftCtx (fun t => mul t e2) (fun s => Step.mulL s)) s1
              have liftRight : Steps (mul (const r1) e2) (mul (const r1) (const r2)) :=
                (liftCtx (fun t => mul (const r1) t) (fun s => Step.mulR (Value.constv r1) s)) s2
              have final : Step (mul (const r1) (const r2)) (const (r1 * r2)) := Step.mulV
              have both : Steps (mul e1 e2) (mul (const r1) (const r2)) := append liftLeft liftRight
              exact Steps.trans both final
  | div e1 e2 ih1 ih2 =>
      intro q h
      cases he2 : eval e2 with
        | none => simp [eval, he2] at h
        | some r2 =>
          cases he1 : eval e1 with
            | none => simp [eval, he1, he2] at h
            | some r1 =>
              -- show r2 ≠ 0, otherwise the eval would be none
              have nz : r2 ≠ 0 := by
                intro z
                simp [eval, he1, he2, z] at h
              have hdiv : some (r1 / r2) = some q := by simpa [eval, he1, he2, nz] using h
              cases hdiv
              have s1 : Steps e1 (const r1) := ih1 (q := r1) he1
              have s2 : Steps e2 (const r2) := ih2 (q := r2) he2
              have liftLeft : Steps (div e1 e2) (div (const r1) e2) :=
                (liftCtx (fun t => div t e2) (fun s => Step.divL s)) s1
              have liftRight : Steps (div (const r1) e2) (div (const r1) (const r2)) :=
                (liftCtx (fun t => div (const r1) t) (fun s => Step.divR (Value.constv r1) s)) s2
              have final : Step (div (const r1) (const r2)) (const (r1 / r2)) := Step.divV nz
              have both : Steps (div e1 e2) (div (const r1) (const r2)) := append liftLeft liftRight
              exact Steps.trans both final
