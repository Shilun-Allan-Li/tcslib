import TCSlib.BooleanAnalysis.LMN.RestrictionFourier

set_option linter.unnecessarySeqFocus false

/-!
# Lower Tail for the Number of Free Coordinates in `U` (Chebyshev)

Under a Bernoulli(`p`)-random restriction with free-coordinate set `J`, the
count `|U ∩ J|` is a `Binomial(|U|, p)` random variable. This file proves the
lower-tail bound needed for the restriction ⇒ Fourier-concentration transfer
(O'Donnell Lemma 4.21):

* `bernoulliRestrProb_card_inter_lt`:
    `Pr[|U ∩ J| < k] ≤ 3/(4k)` whenever `3k ≤ p·|U|` and `k ≥ 1`;
* `bernoulliRestrProb_card_inter_ge`:
    `Pr[|U ∩ J| ≥ k] ≥ 1/4` under the same hypotheses.

O'Donnell uses the Chernoff bound `exp(−2k/3) ≤ 2/3` here; any constant
strictly below 1 works in Lemma 4.21 (the constant only scales the final
concentration `Cε`), so we prove the elementary Chebyshev version instead:
the mean of `|U ∩ J|` is `p·|U| ≥ 3k` and its variance is
`p·|U|·(1−p) ≤ p·|U|`, so missing `k` requires a deviation of at least
`(2/3)·p·|U|`, of probability at most `(9/4)/(p·|U|) ≤ 3/(4k)`.

Both moments are computed from `Pr[T ⊆ J] = p^{|T|`}
(`bernoulliRestrProb_subset_freeVars`), itself an instance of the
per-coordinate factorization `sum_bernoulli_prod` of `RestrictionFourier`.

Also provides `bernoulliRestrProb_not` (complement rule), the general lemma
flagged as missing by the sorry in `CircuitCompression`.
-/

open BooleanAnalysis SwitchingLemma2 LMN
open Classical

noncomputable section

namespace RestrictionFourier

variable {n : ℕ}

/-! ## `Pr[T ⊆ J] = p^{|T|}` -/

/-- The event `T ⊆ freeVars` factors per coordinate. -/
lemma indicator_subset_eq_prod (T : Finset (Fin n)) (ρ : Restriction n) :
    (if T ⊆ ρ.freeVars then (1 : ℝ) else 0)
      = ∏ i : Fin n,
          (if i ∈ T then (if ρ i = none then (1 : ℝ) else 0) else 1) := by
  by_cases h : T ⊆ ρ.freeVars
  · rw [if_pos h]
    symm
    apply Finset.prod_eq_one
    intro i _
    by_cases hiT : i ∈ T
    · have hfree : ρ i = none := mem_freeVars.mp (h hiT)
      simp [hiT, hfree]
    · simp [hiT]
  · rw [if_neg h]
    symm
    obtain ⟨i, hiT, hiJ⟩ := Finset.not_subset.mp h
    apply Finset.prod_eq_zero (Finset.mem_univ i)
    have hfix : ¬ ρ i = none := fun hn => hiJ (mem_freeVars.mpr hn)
    simp [hiT, hfix]

/-- **Free-set marginal**: `Pr[T ⊆ J] = p^{|T|}` under a Bernoulli(`p`)-random
    restriction. (The first-moment half of O'Donnell Proposition 4.17.) -/
theorem bernoulliRestrProb_subset_freeVars (p : ℝ) (T : Finset (Fin n)) :
    bernoulliRestrProb p (fun ρ => T ⊆ ρ.freeVars) = p ^ T.card := by
  unfold bernoulliRestrProb
  rw [Finset.sum_congr rfl fun ρ _ => by rw [indicator_subset_eq_prod T ρ]]
  rw [sum_bernoulli_prod p
    (fun i v => if i ∈ T then (if v = none then (1 : ℝ) else 0) else 1)]
  have hcoord : ∀ i : Fin n,
      (∑ v : Option Bool, varWeight p v *
        (if i ∈ T then (if v = none then (1 : ℝ) else 0) else 1))
      = if i ∈ T then p else 1 := by
    intro i
    by_cases hiT : i ∈ T <;> simp [varWeight, hiT] <;> ring
  rw [Finset.prod_congr rfl fun i _ => hcoord i, Finset.prod_ite_mem,
    Finset.univ_inter, Finset.prod_const]

/-! ## First and second moments of `|U ∩ J|` -/

/-- `|U ∩ J|` as a sum of free-coordinate indicators. -/
lemma card_inter_eq_sum (U : Finset (Fin n)) (ρ : Restriction n) :
    ((U ∩ ρ.freeVars).card : ℝ)
      = ∑ i ∈ U, (if ρ i = none then (1 : ℝ) else 0) := by
  have hfilter : U ∩ ρ.freeVars = U.filter (fun i => ρ i = none) := by
    ext i
    simp [Finset.mem_filter, Finset.mem_inter, mem_freeVars]
  rw [hfilter, Finset.card_filter]
  push_cast
  rfl

/-- Expectation of one free-coordinate indicator. -/
lemma expectation_free_indicator (p : ℝ) (i : Fin n) :
    ∑ ρ : Restriction n, bernoulliRestrWeight p ρ *
      (if ρ i = none then (1 : ℝ) else 0) = p := by
  have h := bernoulliRestrProb_subset_freeVars p ({i} : Finset (Fin n))
  rw [Finset.card_singleton, pow_one] at h
  calc ∑ ρ : Restriction n, bernoulliRestrWeight p ρ *
        (if ρ i = none then (1 : ℝ) else 0)
      = bernoulliRestrProb p (fun ρ => ({i} : Finset (Fin n)) ⊆ ρ.freeVars) := by
        unfold bernoulliRestrProb
        refine Finset.sum_congr rfl fun ρ _ => ?_
        congr 1
        exact if_congr (by simp [Finset.singleton_subset_iff, mem_freeVars])
          rfl rfl
    _ = p := h

/-- Expectation of a product of two distinct free-coordinate indicators. -/
lemma expectation_free_indicator_pair (p : ℝ) (i j : Fin n) (hij : i ≠ j) :
    ∑ ρ : Restriction n, bernoulliRestrWeight p ρ *
      ((if ρ i = none then (1 : ℝ) else 0) *
        (if ρ j = none then (1 : ℝ) else 0)) = p ^ 2 := by
  have h := bernoulliRestrProb_subset_freeVars p ({i, j} : Finset (Fin n))
  rw [Finset.card_insert_of_notMem (by simp [hij]), Finset.card_singleton] at h
  calc ∑ ρ : Restriction n, bernoulliRestrWeight p ρ *
        ((if ρ i = none then (1 : ℝ) else 0) *
          (if ρ j = none then (1 : ℝ) else 0))
      = bernoulliRestrProb p
          (fun ρ => ({i, j} : Finset (Fin n)) ⊆ ρ.freeVars) := by
        unfold bernoulliRestrProb
        refine Finset.sum_congr rfl fun ρ _ => ?_
        congr 1
        by_cases h1 : ρ i = none <;> by_cases h2 : ρ j = none <;>
          simp [Finset.insert_subset_iff, Finset.singleton_subset_iff,
            mem_freeVars, h1, h2]
    _ = p ^ 2 := h

/-- **First moment**: `E[|U ∩ J|] = p·|U|`. -/
lemma expectation_card_inter (p : ℝ) (U : Finset (Fin n)) :
    ∑ ρ : Restriction n, bernoulliRestrWeight p ρ *
      ((U ∩ ρ.freeVars).card : ℝ) = p * U.card := by
  rw [Finset.sum_congr rfl fun ρ _ => by
    rw [card_inter_eq_sum, Finset.mul_sum]]
  rw [Finset.sum_comm]
  rw [Finset.sum_congr rfl fun i _ => expectation_free_indicator p i]
  rw [Finset.sum_const, nsmul_eq_mul, mul_comm]

/-- **Second moment**: `E[|U ∩ J|²] = p·|U| + p²·(|U|² − |U|)`. -/
lemma expectation_card_inter_sq (p : ℝ) (U : Finset (Fin n)) :
    ∑ ρ : Restriction n, bernoulliRestrWeight p ρ *
      ((U ∩ ρ.freeVars).card : ℝ) ^ 2
      = p * U.card + p ^ 2 * ((U.card : ℝ) ^ 2 - U.card) := by
  have hsq : ∀ ρ : Restriction n, bernoulliRestrWeight p ρ *
      ((U ∩ ρ.freeVars).card : ℝ) ^ 2
      = ∑ i ∈ U, ∑ j ∈ U, bernoulliRestrWeight p ρ *
          ((if ρ i = none then (1 : ℝ) else 0) *
            (if ρ j = none then (1 : ℝ) else 0)) := by
    intro ρ
    rw [pow_two, card_inter_eq_sum, Finset.sum_mul_sum, Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ => Finset.mul_sum _ _ _
  rw [Finset.sum_congr rfl fun ρ _ => hsq ρ]
  rw [Finset.sum_comm]
  rw [Finset.sum_congr rfl fun i _ => Finset.sum_comm]
  have hij : ∀ i ∈ U, ∀ j ∈ U,
      (∑ ρ : Restriction n, bernoulliRestrWeight p ρ *
        ((if ρ i = none then (1 : ℝ) else 0) *
          (if ρ j = none then (1 : ℝ) else 0)))
      = if i = j then p else p ^ 2 := by
    intro i _ j _
    by_cases hij : i = j
    · subst hij
      rw [if_pos rfl]
      have hind : ∀ ρ : Restriction n,
          ((if ρ i = none then (1 : ℝ) else 0) *
            (if ρ i = none then (1 : ℝ) else 0))
          = (if ρ i = none then (1 : ℝ) else 0) := by
        intro ρ
        by_cases h : ρ i = none <;> simp [h]
      rw [Finset.sum_congr rfl fun ρ _ => by rw [hind ρ]]
      exact expectation_free_indicator p i
    · rw [if_neg hij]
      exact expectation_free_indicator_pair p i j hij
  rw [Finset.sum_congr rfl fun i hi =>
    Finset.sum_congr rfl fun j hj => hij i hi j hj]
  have hrow : ∀ i ∈ U, ∑ j ∈ U, (if i = j then p else p ^ 2)
      = p ^ 2 * ((U.card : ℝ) - 1) + p := by
    intro i hi
    have hsplit : ∀ j : Fin n, (if i = j then p else p ^ 2)
        = p ^ 2 + (if i = j then p - p ^ 2 else 0) := by
      intro j
      split_ifs <;> ring
    rw [Finset.sum_congr rfl fun j _ => hsplit j, Finset.sum_add_distrib,
      Finset.sum_const, Finset.sum_ite_eq U i (fun _ => p - p ^ 2), if_pos hi,
      nsmul_eq_mul]
    ring
  rw [Finset.sum_congr rfl hrow, Finset.sum_const, nsmul_eq_mul]
  ring

/-- **Variance**: `E[(p·|U| − |U ∩ J|)²] = p·|U|·(1−p)`. -/
lemma variance_card_inter (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (U : Finset (Fin n)) :
    ∑ ρ : Restriction n, bernoulliRestrWeight p ρ *
      (p * U.card - ((U ∩ ρ.freeVars).card : ℝ)) ^ 2
      = p * U.card * (1 - p) := by
  have hexpand : ∀ ρ : Restriction n, bernoulliRestrWeight p ρ *
      (p * U.card - ((U ∩ ρ.freeVars).card : ℝ)) ^ 2
      = (p * U.card) ^ 2 * bernoulliRestrWeight p ρ
        - 2 * (p * U.card) *
            (bernoulliRestrWeight p ρ * ((U ∩ ρ.freeVars).card : ℝ))
        + bernoulliRestrWeight p ρ * ((U ∩ ρ.freeVars).card : ℝ) ^ 2 :=
    fun ρ => by ring
  rw [Finset.sum_congr rfl fun ρ _ => hexpand ρ]
  rw [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum,
    ← Finset.mul_sum]
  rw [expectation_card_inter, expectation_card_inter_sq,
    bernoulliRestrWeight_sum_one p hp0 hp1]
  ring

/-! ## The lower-tail bound -/

/-- **Chebyshev lower tail**: if `3k ≤ p·|U|` and `k ≥ 1`, then
    `Pr[|U ∩ J| < k] ≤ 3/(4k)`. (The Bernoulli-restriction analogue of the
    binomial lower tail used in O'Donnell Lemma 4.21; the textbook's
    `exp(−2k/3)` is replaced by the elementary `3/(4k) ≤ 3/4 < 1`, which
    suffices there.) -/
theorem bernoulliRestrProb_card_inter_lt (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (U : Finset (Fin n)) (k : ℕ) (hk : 1 ≤ k)
    (h3k : 3 * (k : ℝ) ≤ p * U.card) :
    bernoulliRestrProb p (fun ρ => (U ∩ ρ.freeVars).card < k) ≤ 3 / (4 * k) := by
  have hk1 : (1 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk
  have hdenom : 0 < p * U.card - k := by linarith
  have hpt : ∀ ρ : Restriction n,
      (if (U ∩ ρ.freeVars).card < k then (1 : ℝ) else 0)
        ≤ (p * U.card - ((U ∩ ρ.freeVars).card : ℝ)) ^ 2
            / (p * U.card - k) ^ 2 := by
    intro ρ
    split_ifs with h
    · have hX : ((U ∩ ρ.freeVars).card : ℝ) ≤ (k : ℝ) - 1 := by
        have hle : (U ∩ ρ.freeVars).card ≤ k - 1 := Nat.le_sub_one_of_lt h
        calc ((U ∩ ρ.freeVars).card : ℝ) ≤ ((k - 1 : ℕ) : ℝ) := by
              exact_mod_cast hle
          _ = (k : ℝ) - 1 := by
              rw [Nat.cast_sub hk, Nat.cast_one]
      rw [le_div_iff₀ (by positivity), one_mul]
      gcongr
    · positivity
  unfold bernoulliRestrProb
  calc ∑ ρ : Restriction n, bernoulliRestrWeight p ρ *
        (if (U ∩ ρ.freeVars).card < k then (1 : ℝ) else 0)
      ≤ ∑ ρ : Restriction n, bernoulliRestrWeight p ρ *
          ((p * U.card - ((U ∩ ρ.freeVars).card : ℝ)) ^ 2
            / (p * U.card - k) ^ 2) :=
        Finset.sum_le_sum fun ρ _ => mul_le_mul_of_nonneg_left (hpt ρ)
          (bernoulliRestrWeight_nonneg' p hp0 hp1 ρ)
    _ = (∑ ρ : Restriction n, bernoulliRestrWeight p ρ *
          (p * U.card - ((U ∩ ρ.freeVars).card : ℝ)) ^ 2)
            / (p * U.card - k) ^ 2 := by
        rw [Finset.sum_div]
        exact Finset.sum_congr rfl fun ρ _ => (mul_div_assoc _ _ _).symm
    _ = p * U.card * (1 - p) / (p * U.card - k) ^ 2 := by
        rw [variance_card_inter p hp0 hp1 U]
    _ ≤ 3 / (4 * k) := by
        have hs0 : (0 : ℝ) ≤ p * U.card := by linarith
        have hfac : 0 ≤ (p * U.card - 3 * k) * (3 * (p * U.card) - k) :=
          mul_nonneg (by linarith) (by linarith)
        have hdrop : p * U.card * (1 - p) * (4 * k) ≤ 4 * k * (p * U.card) := by
          nlinarith [mul_nonneg (mul_nonneg hs0 hp0) (by linarith : (0:ℝ) ≤ 4 * k)]
        rw [div_le_div_iff₀ (by positivity) (by positivity)]
        nlinarith [hfac, hdrop]

/-! ## Complement rule and the `≥ k` corollary -/

/-- **Complement rule** for Bernoulli-restriction probabilities:
    `Pr[¬E] = 1 − Pr[E]`. -/
lemma bernoulliRestrProb_not (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (event : Restriction n → Prop) [DecidablePred event] :
    bernoulliRestrProb p (fun ρ => ¬ event ρ)
      = 1 - bernoulliRestrProb p event := by
  have hsum : bernoulliRestrProb p (fun ρ => ¬ event ρ)
      + bernoulliRestrProb p event = 1 := by
    unfold bernoulliRestrProb
    rw [← Finset.sum_add_distrib]
    rw [Finset.sum_congr rfl fun ρ _ => ?_]
    · exact bernoulliRestrWeight_sum_one p hp0 hp1
    · by_cases h : event ρ <;> simp [h]
  linarith

/-- If `3k ≤ p·|U|` and `k ≥ 1`, then `Pr[|U ∩ J| ≥ k] ≥ 1/4` — the form
    consumed by the concentration transfer of O'Donnell Lemma 4.21. -/
theorem bernoulliRestrProb_card_inter_ge (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (U : Finset (Fin n)) (k : ℕ) (hk : 1 ≤ k)
    (h3k : 3 * (k : ℝ) ≤ p * U.card) :
    (1 : ℝ) / 4 ≤ bernoulliRestrProb p (fun ρ => k ≤ (U ∩ ρ.freeVars).card) := by
  have hcompl : bernoulliRestrProb p (fun ρ => k ≤ (U ∩ ρ.freeVars).card)
      = 1 - bernoulliRestrProb p (fun ρ => (U ∩ ρ.freeVars).card < k) := by
    rw [← bernoulliRestrProb_not p hp0 hp1
      (fun ρ => (U ∩ ρ.freeVars).card < k)]
    unfold bernoulliRestrProb
    refine Finset.sum_congr rfl fun ρ _ => ?_
    congr 1
    exact if_congr not_lt.symm rfl rfl
  have htail := bernoulliRestrProb_card_inter_lt p hp0 hp1 U k hk h3k
  have hk1 : (1 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk
  have hsmall : 3 / (4 * (k : ℝ)) ≤ 3 / 4 := by
    rw [div_le_div_iff₀ (by positivity) (by norm_num)]
    linarith
  rw [hcompl]
  linarith

end RestrictionFourier
