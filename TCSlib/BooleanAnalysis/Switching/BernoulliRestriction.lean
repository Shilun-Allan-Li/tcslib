import TCSlib.BooleanAnalysis.Switching.Restriction
import Mathlib

/-!
# Bernoulli Random Restriction Model

This file defines the Bernoulli probability model for random restrictions,
where each variable is independently left free with probability `p` and
fixed to `true` or `false` each with probability `(1-p)/2`.

## Main definitions

- `bernoulliRestrWeight p ρ`: the probability of restriction `ρ` under
  Bernoulli parameter `p`.
- `bernoulliRestrProb p event`: the probability that `event` holds under
  the Bernoulli(`p`) restriction model.

## Main results

- `bernoulliRestrWeight_nonneg'`: weights are nonneg when `0 ≤ p ≤ 1`.
- `bernoulliRestrWeight_sum_one`: weights sum to 1.
- `bernoulliRestrProb_le_one'`: probabilities are at most 1.
-/

open Classical SwitchingLemma2

noncomputable section

namespace SwitchingLemma2

variable {n : ℕ}

/-- The probability weight of a restriction `ρ` under the Bernoulli(`p`) model.
    Each free variable contributes `p`, each fixed variable contributes `(1-p)/2`. -/
def bernoulliRestrWeight (p : ℝ) (ρ : Restriction n) : ℝ :=
  p ^ ρ.freeVars.card * ((1 - p) / 2) ^ (n - ρ.freeVars.card)

/-- The probability that a predicate `event` holds under a Bernoulli(`p`)
    random restriction. -/
def bernoulliRestrProb (p : ℝ) (event : Restriction n → Prop)
    [DecidablePred event] : ℝ :=
  ∑ ρ : Restriction n,
    bernoulliRestrWeight p ρ * (if event ρ then 1 else 0)

/-! ## Basic properties -/

lemma bernoulliRestrWeight_nonneg' (p : ℝ) (hp : 0 ≤ p) (hp1 : p ≤ 1)
    (ρ : Restriction n) : 0 ≤ bernoulliRestrWeight p ρ := by
  unfold bernoulliRestrWeight
  apply mul_nonneg
  · exact pow_nonneg hp _
  · exact pow_nonneg (div_nonneg (sub_nonneg.mpr hp1) (by norm_num)) _

/-
The Bernoulli restriction weights sum to 1. This follows from the multinomial
    theorem: `(p + (1-p)/2 + (1-p)/2)^n = 1^n = 1`.
-/
lemma bernoulliRestrWeight_sum_one (p : ℝ) (hp : 0 ≤ p) (hp1 : p ≤ 1) :
    ∑ ρ : Restriction n, bernoulliRestrWeight p ρ = 1 := by
  -- We can rewrite the sum as a product of sums over each variable.
  have h_prod_sum : ∑ ρ : Fin n → Option Bool, p ^ (Finset.univ.filter (fun i => ρ i = none)).card * ((1 - p) / 2) ^ (n - (Finset.univ.filter (fun i => ρ i = none)).card) = ∏ i : Fin n, (∑ ρ_i : Option Bool, (if ρ_i = none then p else (1 - p) / 2)) := by
    rw [ Finset.prod_sum ];
    refine' Finset.sum_bij ( fun ρ _ => fun i _ => ρ i ) _ _ _ _ <;> simp +decide;
    · simp +decide [ funext_iff ];
    · exact fun b => ⟨ fun i => b i ( Finset.mem_univ i ), funext fun i => rfl ⟩;
    · intro a; rw [ Finset.prod_ite ] ; simp +decide [ Finset.filter_not, Finset.card_sdiff ] ;
      exact Or.inl ( by rw [ div_pow ] );
  convert h_prod_sum using 1;
  · unfold bernoulliRestrWeight; congr; ext; simp +decide [ Restriction.freeVars ] ;
  · norm_num [ Finset.sum_ite, Finset.filter_eq', Finset.filter_ne' ];
    have h1 : p + 2 * ((1 - p) / 2) = 1 := by ring
    rw [h1, one_pow]

lemma bernoulliRestrProb_le_one' (p : ℝ) (hp : 0 ≤ p) (hp1 : p ≤ 1)
    (event : Restriction n → Prop) [DecidablePred event] :
    bernoulliRestrProb p event ≤ 1 := by
  unfold bernoulliRestrProb
  calc ∑ ρ : Restriction n, bernoulliRestrWeight p ρ * (if event ρ then 1 else 0)
      ≤ ∑ ρ : Restriction n, bernoulliRestrWeight p ρ := by
        apply Finset.sum_le_sum
        intro ρ _
        have h1 : (if event ρ then (1:ℝ) else 0) ≤ 1 := by split_ifs <;> norm_num
        calc bernoulliRestrWeight p ρ * (if event ρ then 1 else 0)
            ≤ bernoulliRestrWeight p ρ * 1 :=
              mul_le_mul_of_nonneg_left h1 (bernoulliRestrWeight_nonneg' p hp hp1 ρ)
          _ = bernoulliRestrWeight p ρ := by ring
    _ = 1 := bernoulliRestrWeight_sum_one p hp hp1

end SwitchingLemma2

end