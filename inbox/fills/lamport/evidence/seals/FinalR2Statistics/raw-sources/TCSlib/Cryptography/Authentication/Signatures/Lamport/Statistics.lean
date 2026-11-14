/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TCSlib.Cryptography.Authentication.Signatures.Lamport.Planted
import TCSlib.Cryptography.Authentication.Signatures.Lamport.Averaging

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Sampling a planted coordinate independently

## Main definitions

None.

## Main results

* `coordinate_reduction_bound`: a pointwise favorable-position bound and a
  coordinate-invariant reduction give the same bound with the challenge sampled
  independently of the table.

## References

* [PS10] R. Pass, a. shelat, *A Course in Cryptography*, lecture notes, 3rd ed.,
  January 2010, proof of Theorem 137.2.
-/

namespace TCSlib.Cryptography.Authentication.LamportFill

open TCSlib.Cryptography.Games
open scoped Classical

-- Keep elaboration on the published probability readers.
run_cmd do
  for n in [``ProbComp.expect, ``ProbComp.sample, ``OracleComp.bind] do
    let status ← Lean.Elab.Command.liftCoreM <| Lean.getReducibilityStatus n
    unless status == .irreducible do
      let id := Lean.mkIdent n
      Lean.Elab.Command.elabCommand (← `(command| attribute [local irreducible] $id:ident))

/-- Suppose every successful honest run has favorable position mass at least `b`, and
every successful favorable run makes a reduction succeed when challenged at its own
table coordinate. If the reduction ignores that original coordinate, the average
reduction success for an independent challenge is at least `b` times honest success.

**Proof sketch.** Bound the reduction's position average pointwise by favorable mass
on successful honest runs, and by zero on unsuccessful ones. Average over tables and
forger coins. Exchange the position average with those samples. Finally use the
coordinate-invariance hypothesis to sample the challenge preimage independently
(`ProbComp.expect_sample_coord`). This is generic probability glue for the planting
argument of [PS10, Theorem 137.2]. -/
theorem coordinate_reduction_bound {n : ℕ} [Nonempty (Fin n)]
    {ρ : Type} [Fintype ρ] [Nonempty ρ]
    (P : Table n → ρ → Prop)
    (Q : Table n → ρ → (Fin n × Bool) → Prop)
    (R : (Fin n → Bool) → Table n → ρ → (Fin n × Bool) → Prop)
    (b : ℝ)
    (hgood : ∀ T r, P T r → b ≤
      ProbComp.expect (ProbComp.sample (Fin n × Bool))
        (fun p => if Q T r p then (1 : ℝ) else 0))
    (himp : ∀ T r p, P T r → Q T r p → R (T p) T r p)
    (hinv : ∀ x x' T r p,
      R x (Function.update T p x') r p ↔ R x T r p) :
    b * ProbComp.expect (ProbComp.sample (Table n))
        (fun T => ProbComp.expect (ProbComp.sample ρ)
          (fun r => if P T r then (1 : ℝ) else 0)) ≤
      ProbComp.expect (ProbComp.sample (Fin n × Bool)) (fun p =>
        ProbComp.expect (ProbComp.sample (Fin n → Bool)) (fun x =>
          ProbComp.expect (ProbComp.sample (Table n)) (fun T =>
            ProbComp.expect (ProbComp.sample ρ)
              (fun r => if R x T r p then (1 : ℝ) else 0)))) := by
  have hpoint (T : Table n) (r : ρ) :
      b * (if P T r then (1 : ℝ) else 0) ≤
        ProbComp.expect (ProbComp.sample (Fin n × Bool))
          (fun p => if R (T p) T r p then (1 : ℝ) else 0) := by
    by_cases hp : P T r
    · simp only [hp, if_true, mul_one]
      refine (hgood T r hp).trans (ProbComp.expect_mono _ fun p => ?_)
      by_cases hq : Q T r p
      · have hr := himp T r p hp hq
        simp only [hq, hr, if_true, le_refl]
      · simp only [hq, if_false]
        split_ifs <;> positivity
    · simp only [hp, if_false, mul_zero]
      exact ProbComp.expect_nonneg _ (fun p => by split_ifs <;> positivity)
  calc
    b * ProbComp.expect (ProbComp.sample (Table n))
        (fun T => ProbComp.expect (ProbComp.sample ρ)
          (fun r => if P T r then (1 : ℝ) else 0)) =
      ProbComp.expect (ProbComp.sample (Table n))
        (fun T => ProbComp.expect (ProbComp.sample ρ)
          (fun r => b * (if P T r then (1 : ℝ) else 0))) := by
      symm
      calc
        ProbComp.expect (ProbComp.sample (Table n))
            (fun T => ProbComp.expect (ProbComp.sample ρ)
              (fun r => b * (if P T r then (1 : ℝ) else 0))) =
          ProbComp.expect (ProbComp.sample (Table n))
            (fun T => b * ProbComp.expect (ProbComp.sample ρ)
              (fun r => if P T r then (1 : ℝ) else 0)) := by
          apply congrArg (ProbComp.expect (ProbComp.sample (Table n)))
          funext T
          exact ProbComp.expect_const_mul (ProbComp.sample ρ) b
            (fun r => if P T r then (1 : ℝ) else 0)
        _ = b * ProbComp.expect (ProbComp.sample (Table n))
            (fun T => ProbComp.expect (ProbComp.sample ρ)
              (fun r => if P T r then (1 : ℝ) else 0)) :=
          ProbComp.expect_const_mul (ProbComp.sample (Table n)) b
            (fun T => ProbComp.expect (ProbComp.sample ρ)
              (fun r => if P T r then (1 : ℝ) else 0))
    _ ≤ ProbComp.expect (ProbComp.sample (Table n))
        (fun T => ProbComp.expect (ProbComp.sample ρ)
          (fun r => ProbComp.expect (ProbComp.sample (Fin n × Bool))
            (fun p => if R (T p) T r p then (1 : ℝ) else 0))) :=
      ProbComp.expect_mono _ (fun T => ProbComp.expect_mono _ (hpoint T))
    _ = ProbComp.expect (ProbComp.sample (Table n))
        (fun T => ProbComp.expect (ProbComp.sample (Fin n × Bool))
          (fun p => ProbComp.expect (ProbComp.sample ρ)
            (fun r => if R (T p) T r p then (1 : ℝ) else 0))) := by
      apply congrArg (ProbComp.expect (ProbComp.sample (Table n)))
      funext T
      exact ProbComp.expect_sample_comm
        (fun r p => if R (T p) T r p then (1 : ℝ) else 0)
    _ = ProbComp.expect (ProbComp.sample (Fin n × Bool))
        (fun p => ProbComp.expect (ProbComp.sample (Table n))
          (fun T => ProbComp.expect (ProbComp.sample ρ)
            (fun r => if R (T p) T r p then (1 : ℝ) else 0))) :=
      ProbComp.expect_sample_comm
        (fun T p => ProbComp.expect (ProbComp.sample ρ)
          (fun r => if R (T p) T r p then (1 : ℝ) else 0))
    _ = ProbComp.expect (ProbComp.sample (Fin n × Bool)) (fun p =>
        ProbComp.expect (ProbComp.sample (Fin n → Bool)) (fun x =>
          ProbComp.expect (ProbComp.sample (Table n)) (fun T =>
            ProbComp.expect (ProbComp.sample ρ)
              (fun r => if R x T r p then (1 : ℝ) else 0)))) := by
      apply congrArg (ProbComp.expect (ProbComp.sample (Fin n × Bool)))
      funext p
      exact ProbComp.expect_sample_coord p
        (fun x T => ProbComp.expect (ProbComp.sample ρ)
          (fun r => if R x T r p then (1 : ℝ) else 0))
        (fun x x' T => by
          apply congrArg (ProbComp.expect (ProbComp.sample ρ))
          funext r
          rw [hinv x x' T r p])

end TCSlib.Cryptography.Authentication.LamportFill
