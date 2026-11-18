/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TCSlib.Cryptography.Pairing.Exponents
import TCSlib.Cryptography.Games.Probability
import TCSlib.Cryptography.Games.Bridges.Experiments
import TCSlib.Cryptography.OneWayFunctions.Basic

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Diagonal masks over finite fields

## Main definitions

This module adds no algorithms or samplers.

## Main results

* `dlinDiagonal_random_gap_le`: the exact bad-diagonal bound for bounded tests.

## References

* [GJLS21] R. Gay, A. Jain, H. Lin, A. Sahai, *Indistinguishability Obfuscation from
  Simple-to-State Hard Problems: New Assumptions, New Techniques, and Simplification*,
  EUROCRYPT 2021; ePrint 2020/764, revision of 3 January 2025, Definition 3.3.
* [JLS26] A. Jain, H. Lin, A. Sahai, *Indistinguishability Obfuscation from Well-Founded
  Assumptions*, Journal of the ACM 73(1), Article 1, 2026, Section 1.1.
-/

namespace TCSlib.Cryptography.Pairing

open TCSlib.Cryptography.Games

/-- Uniform scalar responses and responses multiplied by two independent diagonal masks
have expectation gap at most `2/N - 1/N²` for every test with values in `[0,1]`, where `N`
is the finite field's cardinality. This is fixed-field probability glue for the random-law
comparison [GJLS21, Definition 3.3, p.18; JLS26, §1.1, p.3].

**Proof sketch.** Fix the diagonal pair. If both entries are nonzero, their coordinatewise
multiplication permutations preserve the uniform response law. Otherwise each bounded
expectation lies in `[0,1]`, so its gap is at most one. Average the resulting bad-event
indicator with `abs_expect_sub_le_expect`. Reindex the two diagonal coordinates as a product
and evaluate the exact bad mass `1/N + (1-1/N)/N = 2/N - 1/N²`, using existing singleton
probability and sample/Fubini readers. No sampler is constructed. -/
theorem dlinDiagonal_random_gap_le {K : Type} [Field K] [Fintype K]
    (H : (Fin 2 → K) → (Fin 3 → K) → ℝ)
    (hH0 : ∀ ab u, 0 ≤ H ab u) (hH1 : ∀ ab u, H ab u ≤ 1) :
    |ProbComp.expect (ProbComp.sample (Fin 2 → K))
        (fun ab => ProbComp.expect (ProbComp.sample (Fin 3 → K)) (H ab)) -
      ProbComp.expect (ProbComp.sample (Fin 2 → K))
        (fun ab => ProbComp.expect (ProbComp.sample (Fin 2 → K))
          (fun rs => ProbComp.expect (ProbComp.sample K)
            (fun t => H ab ![ab 0 * rs 0, ab 1 * rs 1, t])))| ≤
      2 / (Fintype.card K : ℝ) - 1 / (Fintype.card K : ℝ) ^ 2 := by
  classical
  let A : (Fin 2 → K) → ℝ := fun ab =>
    ProbComp.expect (ProbComp.sample (Fin 3 → K)) (H ab)
  let B : (Fin 2 → K) → ℝ := fun ab =>
    ProbComp.expect (ProbComp.sample (Fin 2 → K)) fun rs =>
      ProbComp.expect (ProbComp.sample K) fun t => H ab ![ab 0 * rs 0, ab 1 * rs 1, t]
  let bad : (Fin 2 → K) → Prop := fun ab => ab 0 = 0 ∨ ab 1 = 0
  have hA0 (ab : Fin 2 → K) : 0 ≤ A ab := ProbComp.expect_nonneg _ (hH0 ab)
  have hA1 (ab : Fin 2 → K) : A ab ≤ 1 :=
    calc
      A ab ≤ ProbComp.expect (ProbComp.sample (Fin 3 → K)) (fun _ => 1) :=
        ProbComp.expect_mono _ (hH1 ab)
      _ = 1 := ProbComp.expect_const _ 1
  have hB0 (ab : Fin 2 → K) : 0 ≤ B ab :=
    ProbComp.expect_nonneg _ (fun rs => ProbComp.expect_nonneg _
      (fun t => hH0 ab ![ab 0 * rs 0, ab 1 * rs 1, t]))
  have hB1 (ab : Fin 2 → K) : B ab ≤ 1 :=
    calc
      B ab ≤ ProbComp.expect (ProbComp.sample (Fin 2 → K)) (fun _ => 1) :=
        ProbComp.expect_mono _ (fun rs =>
          calc
            ProbComp.expect (ProbComp.sample K)
                (fun t => H ab ![ab 0 * rs 0, ab 1 * rs 1, t]) ≤
              ProbComp.expect (ProbComp.sample K) (fun _ => 1) :=
              ProbComp.expect_mono _ (fun t => hH1 ab ![ab 0 * rs 0, ab 1 * rs 1, t])
            _ = 1 := ProbComp.expect_const _ 1)
      _ = 1 := ProbComp.expect_const _ 1
  have hGood : ∀ ab : Fin 2 → K, ab 0 ≠ 0 → ab 1 ≠ 0 → A ab = B ab := by
    intro ab ha0 ha1
    let scale : (Fin 2 → K) ≃ (Fin 2 → K) :=
      (finTwoArrowEquiv K).trans
        ((Equiv.prodCongr (Equiv.mulLeft₀ (ab 0) ha0)
          (Equiv.mulLeft₀ (ab 1) ha1)).trans ((finTwoArrowEquiv K).symm))
    let e : ((Fin 2 → K) × K) ≃ (Fin 3 → K) :=
      (Equiv.prodCongr scale (Equiv.refl K)).trans ((Fin.succFunEquiv K 2).symm)
    have hShape (rs : Fin 2 → K) (t : K) :
        e (rs, t) = ![ab 0 * rs 0, ab 1 * rs 1, t] := ?_
    swap
    · funext i
      fin_cases i <;> rfl
    dsimp only [A, B]
    rw [← ProbComp.expect_sample_equiv e (H ab), ← Bridge.expect_sample_pair]
    simp only [ProbComp.expect_bind, ProbComp.expect_pure, hShape]
  have hBadMass :
      ProbComp.expect (ProbComp.sample (Fin 2 → K))
          (fun ab => if bad ab then (1 : ℝ) else 0) =
        2 / (Fintype.card K : ℝ) - 1 / (Fintype.card K : ℝ) ^ 2 := by
    classical
    let c : ℝ := 1 / (Fintype.card K : ℝ)
    have hN : (Fintype.card K : ℝ) ≠ 0 := Nat.cast_ne_zero.2 Fintype.card_ne_zero
    have hZero :
        ProbComp.expect (ProbComp.sample K) (fun a => if a = 0 then (1 : ℝ) else 0) = c :=
      (ProbComp.prob_eq_expect (ProbComp.sample K) (fun a : K => a = 0)).symm.trans
        ((Bridge.prob_sample_eq_uprob (fun a : K => a = 0)).trans
          (TCSlib.Cryptography.OneWay.uprob_eq_one_div_card (0 : K)))
    have hInner (a : K) :
        ProbComp.expect (ProbComp.sample K)
            (fun b => if a = 0 ∨ b = 0 then (1 : ℝ) else 0) =
          c + (1 - c) * (if a = 0 then (1 : ℝ) else 0) := ?_
    swap
    · by_cases ha : a = 0
      · have hF : (fun b : K => if a = 0 ∨ b = 0 then (1 : ℝ) else 0) =
            (fun _ => 1) := funext (fun b => if_pos (Or.inl ha))
        rw [hF, ProbComp.expect_const, if_pos ha]
        ring
      · simpa only [ha, false_or, ite_false, mul_zero, add_zero] using hZero
    dsimp only [bad]
    rw [← ProbComp.expect_sample_equiv (finTwoArrowEquiv K).symm
      (fun ab : Fin 2 → K => if ab 0 = 0 ∨ ab 1 = 0 then (1 : ℝ) else 0),
      ← Bridge.expect_sample_pair]
    simp only [ProbComp.expect_bind, ProbComp.expect_pure, finTwoArrowEquiv_symm_apply,
      Matrix.cons_val_zero, Matrix.cons_val_one]
    simp only [hInner]
    rw [ProbComp.expect_add, ProbComp.expect_const, ProbComp.expect_const_mul, hZero]
    dsimp only [c]
    field_simp [hN] <;> ring
  have hPoint : ∀ ab : Fin 2 → K,
      |A ab - B ab| ≤ if bad ab then (1 : ℝ) else 0 := ?_
  swap
  · intro ab
    by_cases hb : bad ab
    · rw [if_pos hb, abs_le]
      constructor <;> linarith [hA0 ab, hA1 ab, hB0 ab, hB1 ab]
    · have ha0 : ab 0 ≠ 0 := fun h => hb (Or.inl h)
      have ha1 : ab 1 ≠ 0 := fun h => hb (Or.inr h)
      simpa only [if_neg hb, hGood ab ha0 ha1, sub_self, abs_zero] using
        (le_refl (0 : ℝ))
  have hAverage := ProbComp.abs_expect_sub_le_expect
    (ProbComp.sample (Fin 2 → K)) hPoint
  rw [hBadMass] at hAverage
  exact hAverage

end TCSlib.Cryptography.Pairing
