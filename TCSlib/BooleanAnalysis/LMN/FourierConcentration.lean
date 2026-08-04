import TCSlib.BooleanAnalysis.LMN.RestrictionCardTail

/-!
# Fourier Concentration from Random Restrictions (O'Donnell Lemma 4.21)

**Lemma 4.21** (O'Donnell, *Analysis of Boolean Functions*): let
`f : {0,1}ⁿ → {0,1}` and let `ρ` be a Bernoulli(`p`)-random restriction
(each coordinate free with probability `p`). Fix `k ≥ 1` and write
`ε = Pr[DT(f_ρ) ≥ k]`. Then the Fourier spectrum of (the ±1-encoding of) `f`
is `4ε`-concentrated up to degree `3k/p`:

  `∑_{|U| ≥ 3k/p} f̂(U)² ≤ 4ε`   (`odonnell_lemma_4_21`, with the
  degree condition stated division-free as `3k ≤ p·|U|`).

The constant is `4` rather than O'Donnell's `3` because the binomial lower
tail is proved by Chebyshev (`Pr[|U ∩ J| ≥ k] ≥ 1/4`,
`bernoulliRestrProb_card_inter_ge`) instead of Chernoff; the constant is
immaterial downstream.

## Proof structure

1. **Pointwise** (`hpt`): for every restriction `ρ`, the Fourier weight of
   `f_ρ` at degrees `≥ k` is at most `1[DT(f_ρ) ≥ k]` — if `DT(f_ρ) < k`
   the weight is 0 by Proposition 3.16 (`degree_le_dtDepth`), and it is
   always at most the total weight 1 (`parseval_pm_one`).
2. **Average** over `ρ`: `∑_{|S| ≥ k} E_ρ[f̂_ρ(S)²] ≤ ε`.
3. **Rewrite** the left side via Proposition 4.17
   (`expectation_fourierCoeff_sq_restrictBF` + partitioning `Pr[U∩J = S]`
   over `S`) as `∑_U f̂(U)² · Pr[|U ∩ J| ≥ k]`
   (`sum_tail_expectation_eq`).
4. **Conclude**: for `U` with `3k ≤ p·|U|` the probability is `≥ 1/4`, so
   `(1/4)·∑_{3k ≤ p·|U|} f̂(U)² ≤ ε`.
-/

open BooleanAnalysis SwitchingLemma2 LMN
open Classical

noncomputable section

namespace RestrictionFourier

variable {n : ℕ}

/-! ## Small helpers -/

/-- The ±1-encoding of a Boolean-valued function is ±1-valued. -/
lemma isPmOne_boolToSign (g : (Fin n → Bool) → Bool) :
    isPmOne (fun x => boolToSign (g x)) := by
  intro x
  cases hgx : g x
  · left
    simp [boolToSign, hgx]
  · right
    simp [boolToSign, hgx]

/-- Bernoulli-restriction probabilities are nonnegative. -/
lemma bernoulliRestrProb_nonneg (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (event : Restriction n → Prop) [DecidablePred event] :
    0 ≤ bernoulliRestrProb p event := by
  unfold bernoulliRestrProb
  refine Finset.sum_nonneg fun ρ _ => mul_nonneg
    (bernoulliRestrWeight_nonneg' p hp0 hp1 ρ) ?_
  split_ifs <;> norm_num

/-- Partition rule: summing `Pr[U ∩ J = S]` over all `S` with `|S| ≥ k`
    gives `Pr[|U ∩ J| ≥ k]`. -/
lemma sum_prob_inter_eq_card_ge (p : ℝ) (U : Finset (Fin n)) (k : ℕ) :
    ∑ S : Finset (Fin n),
        (if k ≤ S.card
          then bernoulliRestrProb p (fun ρ => U ∩ ρ.freeVars = S) else 0)
      = bernoulliRestrProb p (fun ρ => k ≤ (U ∩ ρ.freeVars).card) := by
  have hper : ∀ ρ : Restriction n, (∑ S : Finset (Fin n),
      (if k ≤ S.card then bernoulliRestrWeight p ρ *
        (if U ∩ ρ.freeVars = S then (1 : ℝ) else 0) else 0))
      = bernoulliRestrWeight p ρ *
        (if k ≤ (U ∩ ρ.freeVars).card then (1 : ℝ) else 0) := by
    intro ρ
    have hcomb : ∀ S : Finset (Fin n),
        (if k ≤ S.card then bernoulliRestrWeight p ρ *
          (if U ∩ ρ.freeVars = S then (1 : ℝ) else 0) else 0)
        = if U ∩ ρ.freeVars = S
            then (if k ≤ S.card then bernoulliRestrWeight p ρ else 0)
            else 0 := by
      intro S
      split_ifs <;> simp
    rw [Finset.sum_congr rfl fun S _ => hcomb S, Finset.sum_ite_eq,
      if_pos (Finset.mem_univ _)]
    split_ifs <;> simp
  have hpush : ∀ S : Finset (Fin n),
      (if k ≤ S.card then ∑ ρ : Restriction n, bernoulliRestrWeight p ρ *
        (if U ∩ ρ.freeVars = S then (1 : ℝ) else 0) else 0)
      = ∑ ρ : Restriction n, (if k ≤ S.card then bernoulliRestrWeight p ρ *
          (if U ∩ ρ.freeVars = S then (1 : ℝ) else 0) else 0) := by
    intro S
    split_ifs
    · rfl
    · exact Finset.sum_const_zero.symm
  unfold bernoulliRestrProb
  rw [Finset.sum_congr rfl fun S _ => hpush S, Finset.sum_comm]
  exact Finset.sum_congr rfl fun ρ _ => hper ρ

/-! ## Step 3: the expectation identity in aggregated form -/

/-- `∑_{|S| ≥ k} E_ρ[f̂_ρ(S)²] = ∑_U f̂(U)² · Pr[|U ∩ J| ≥ k]`
    (Proposition 4.17, summed over the high-degree frequencies). -/
lemma sum_tail_expectation_eq (p : ℝ) (F : BooleanFunc n) (k : ℕ) :
    ∑ S : Finset (Fin n), (if k ≤ S.card then
        ∑ ρ : Restriction n, bernoulliRestrWeight p ρ *
          fourierCoeff (restrictBF F ρ) S ^ 2
      else 0)
    = ∑ U : Finset (Fin n), fourierCoeff F U ^ 2 *
        bernoulliRestrProb p (fun ρ => k ≤ (U ∩ ρ.freeVars).card) := by
  have h417 : ∀ S : Finset (Fin n),
      (∑ ρ : Restriction n, bernoulliRestrWeight p ρ *
        fourierCoeff (restrictBF F ρ) S ^ 2)
      = ∑ U : Finset (Fin n),
          bernoulliRestrProb p (fun ρ => U ∩ ρ.freeVars = S) *
            fourierCoeff F U ^ 2 := by
    intro S
    rw [expectation_fourierCoeff_sq_restrictBF]
    refine Finset.sum_congr rfl fun U _ => ?_
    rw [bernoulliRestrProb_inter_freeVars]
    split_ifs <;> ring
  calc ∑ S : Finset (Fin n), (if k ≤ S.card then
          ∑ ρ : Restriction n, bernoulliRestrWeight p ρ *
            fourierCoeff (restrictBF F ρ) S ^ 2 else 0)
      = ∑ S : Finset (Fin n), (if k ≤ S.card then
          ∑ U : Finset (Fin n),
            bernoulliRestrProb p (fun ρ => U ∩ ρ.freeVars = S) *
              fourierCoeff F U ^ 2 else 0) := by
        refine Finset.sum_congr rfl fun S _ => ?_
        split_ifs
        · exact h417 S
        · rfl
    _ = ∑ S : Finset (Fin n), ∑ U : Finset (Fin n),
          (if k ≤ S.card then
            bernoulliRestrProb p (fun ρ => U ∩ ρ.freeVars = S) *
              fourierCoeff F U ^ 2 else 0) := by
        refine Finset.sum_congr rfl fun S _ => ?_
        split_ifs
        · rfl
        · exact Finset.sum_const_zero.symm
    _ = ∑ U : Finset (Fin n), ∑ S : Finset (Fin n),
          (if k ≤ S.card then
            bernoulliRestrProb p (fun ρ => U ∩ ρ.freeVars = S) *
              fourierCoeff F U ^ 2 else 0) := Finset.sum_comm
    _ = ∑ U : Finset (Fin n), fourierCoeff F U ^ 2 *
          ∑ S : Finset (Fin n), (if k ≤ S.card then
            bernoulliRestrProb p (fun ρ => U ∩ ρ.freeVars = S) else 0) := by
        refine Finset.sum_congr rfl fun U _ => ?_
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun S _ => ?_
        split_ifs <;> ring
    _ = ∑ U : Finset (Fin n), fourierCoeff F U ^ 2 *
          bernoulliRestrProb p (fun ρ => k ≤ (U ∩ ρ.freeVars).card) := by
        refine Finset.sum_congr rfl fun U _ => ?_
        rw [sum_prob_inter_eq_card_ge]

/-! ## The main theorem -/

/-- **O'Donnell Lemma 4.21** (with Chebyshev constant): if
    `ε = Pr[DT(f_ρ) ≥ k]` under a Bernoulli(`p`)-random restriction, then
    the Fourier spectrum of the ±1-encoding of `f` is `4ε`-concentrated on
    degrees below `3k/p`:

      `∑_{U : 3k ≤ p·|U|} f̂(U)² ≤ 4ε`. -/
theorem odonnell_lemma_4_21 (f : (Fin n → Bool) → Bool) (p : ℝ)
    (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (k : ℕ) (hk : 1 ≤ k) :
    ∑ U : Finset (Fin n),
        (if 3 * (k : ℝ) ≤ p * U.card
          then fourierCoeff (fun x => boolToSign (f x)) U ^ 2 else 0)
      ≤ 4 * bernoulliRestrProb p (fun ρ => k ≤ dtDepth (restrictFn f ρ)) := by
  -- Step 1: pointwise, high-degree weight of `f_ρ` ≤ 1[DT(f_ρ) ≥ k].
  have hpt : ∀ ρ : Restriction n,
      (∑ S : Finset (Fin n), if k ≤ S.card then
        fourierCoeff (restrictBF (fun x => boolToSign (f x)) ρ) S ^ 2 else 0)
      ≤ (if k ≤ dtDepth (restrictFn f ρ) then (1 : ℝ) else 0) := by
    intro ρ
    split_ifs with hdt
    · calc (∑ S : Finset (Fin n), if k ≤ S.card then
            fourierCoeff (restrictBF (fun x => boolToSign (f x)) ρ) S ^ 2
            else 0)
          ≤ ∑ S : Finset (Fin n),
              fourierCoeff (restrictBF (fun x => boolToSign (f x)) ρ) S ^ 2 := by
            refine Finset.sum_le_sum fun S _ => ?_
            split_ifs
            · exact le_rfl
            · positivity
        _ = 1 := by
            rw [restrictBF_boolToSign]
            exact parseval_pm_one _ (isPmOne_boolToSign _)
    · push_neg at hdt
      have hdeg := DecisionTree.degree_le_dtDepth (restrictFn f ρ)
      refine le_of_eq (Finset.sum_eq_zero fun S _ => ?_)
      split_ifs with hS
      · have hzero : fourierCoeff
            (restrictBF (fun x => boolToSign (f x)) ρ) S = 0 := by
          by_contra hne
          rw [restrictBF_boolToSign] at hne
          have hcard := hdeg S hne
          omega
        rw [hzero]
        norm_num
      · rfl
  -- Step 2: average over ρ.
  have havg : (∑ S : Finset (Fin n), if k ≤ S.card then
        ∑ ρ : Restriction n, bernoulliRestrWeight p ρ *
          fourierCoeff (restrictBF (fun x => boolToSign (f x)) ρ) S ^ 2
        else 0)
      ≤ bernoulliRestrProb p (fun ρ => k ≤ dtDepth (restrictFn f ρ)) := by
    have hswap : (∑ S : Finset (Fin n), if k ≤ S.card then
          ∑ ρ : Restriction n, bernoulliRestrWeight p ρ *
            fourierCoeff (restrictBF (fun x => boolToSign (f x)) ρ) S ^ 2
          else 0)
        = ∑ ρ : Restriction n, bernoulliRestrWeight p ρ *
            ∑ S : Finset (Fin n), (if k ≤ S.card then
              fourierCoeff (restrictBF (fun x => boolToSign (f x)) ρ) S ^ 2
              else 0) := by
      calc (∑ S : Finset (Fin n), if k ≤ S.card then
            ∑ ρ : Restriction n, bernoulliRestrWeight p ρ *
              fourierCoeff (restrictBF (fun x => boolToSign (f x)) ρ) S ^ 2
            else 0)
          = ∑ S : Finset (Fin n), ∑ ρ : Restriction n,
              (if k ≤ S.card then bernoulliRestrWeight p ρ *
                fourierCoeff (restrictBF (fun x => boolToSign (f x)) ρ) S ^ 2
                else 0) := by
            refine Finset.sum_congr rfl fun S _ => ?_
            split_ifs
            · rfl
            · exact Finset.sum_const_zero.symm
        _ = ∑ ρ : Restriction n, ∑ S : Finset (Fin n),
              (if k ≤ S.card then bernoulliRestrWeight p ρ *
                fourierCoeff (restrictBF (fun x => boolToSign (f x)) ρ) S ^ 2
                else 0) := Finset.sum_comm
        _ = ∑ ρ : Restriction n, bernoulliRestrWeight p ρ *
              ∑ S : Finset (Fin n), (if k ≤ S.card then
                fourierCoeff (restrictBF (fun x => boolToSign (f x)) ρ) S ^ 2
                else 0) := by
            refine Finset.sum_congr rfl fun ρ _ => ?_
            rw [Finset.mul_sum]
            refine Finset.sum_congr rfl fun S _ => ?_
            split_ifs <;> ring
    rw [hswap]
    unfold bernoulliRestrProb
    exact Finset.sum_le_sum fun ρ _ => mul_le_mul_of_nonneg_left (hpt ρ)
      (bernoulliRestrWeight_nonneg' p hp0 hp1 ρ)
  -- Steps 2+3 combined: Σ_U f̂(U)²·Pr[|U∩J| ≥ k] ≤ ε.
  have hmain : (∑ U : Finset (Fin n),
        fourierCoeff (fun x => boolToSign (f x)) U ^ 2 *
          bernoulliRestrProb p (fun ρ => k ≤ (U ∩ ρ.freeVars).card))
      ≤ bernoulliRestrProb p (fun ρ => k ≤ dtDepth (restrictFn f ρ)) := by
    rw [← sum_tail_expectation_eq p (fun x => boolToSign (f x)) k]
    exact havg
  -- Step 4: on high-degree U's the probability is at least 1/4.
  have hterm : ∀ U : Finset (Fin n),
      (if 3 * (k : ℝ) ≤ p * U.card
        then fourierCoeff (fun x => boolToSign (f x)) U ^ 2 else 0)
      ≤ 4 * (fourierCoeff (fun x => boolToSign (f x)) U ^ 2 *
          bernoulliRestrProb p (fun ρ => k ≤ (U ∩ ρ.freeVars).card)) := by
    intro U
    split_ifs with hU
    · have hge := bernoulliRestrProb_card_inter_ge p hp0 hp1 U k hk hU
      have hmul := mul_le_mul_of_nonneg_left hge
        (sq_nonneg (fourierCoeff (fun x => boolToSign (f x)) U))
      linarith
    · exact mul_nonneg (by norm_num) (mul_nonneg (sq_nonneg _)
        (bernoulliRestrProb_nonneg p hp0 hp1 _))
  calc ∑ U : Finset (Fin n),
        (if 3 * (k : ℝ) ≤ p * U.card
          then fourierCoeff (fun x => boolToSign (f x)) U ^ 2 else 0)
      ≤ ∑ U : Finset (Fin n),
          4 * (fourierCoeff (fun x => boolToSign (f x)) U ^ 2 *
            bernoulliRestrProb p (fun ρ => k ≤ (U ∩ ρ.freeVars).card)) :=
        Finset.sum_le_sum fun U _ => hterm U
    _ = 4 * ∑ U : Finset (Fin n),
          fourierCoeff (fun x => boolToSign (f x)) U ^ 2 *
            bernoulliRestrProb p (fun ρ => k ≤ (U ∩ ρ.freeVars).card) := by
        rw [Finset.mul_sum]
    _ ≤ 4 * bernoulliRestrProb p (fun ρ => k ≤ dtDepth (restrictFn f ρ)) := by
        linarith

end RestrictionFourier
