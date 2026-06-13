import TCSlib.BooleanAnalysis.Switching.BernoulliRestriction
import Mathlib

/-!
# Bernoulli Restriction Cost

This file proves that switching from the fixed-size restriction model `R_k`
(uniform over restrictions with exactly `k` free variables) to the Bernoulli
restriction model `R_p` does not cost anything asymptotically.

## Main results

- `bernoulli_restriction_cost`: If `Pr_{R_k}[bad] ≤ (5kw/n)^s` for every `k`,
  then `Pr_{R_p}[bad] ≤ (10pw)^s + e^{-np/3}`.
- `bernoulli_restriction_asymptotic`: The `e^{-np/3}` term vanishes as
  `n → ∞`, so asymptotically the Bernoulli model is as good as the fixed-size
  model.
-/

open SwitchingLemma2
noncomputable section

namespace BernoulliCost

variable {n : ℕ}

/-! ## Definitions -/

/-- The set of restrictions on `n` variables with exactly `k` free variables. -/
def fixedSizeRestrs (n k : ℕ) : Finset (Restriction n) :=
  Finset.univ.filter (fun ρ : Restriction n => ρ.freeVars.card = k)

/-- The probability of an event under the fixed-size restriction model `R_k`
    (uniform over restrictions with exactly `k` free variables). -/
def fixedSizeRestrProb (event : Restriction n → Prop) [DecidablePred event]
    (k : ℕ) : ℝ :=
  ↑((fixedSizeRestrs n k).filter (fun ρ => event ρ)).card / ↑(fixedSizeRestrs n k).card

/-- Binomial probability mass function: `Pr[Bin(n,p) = k] = C(n,k) p^k (1-p)^{n-k}`. -/
def binomialPMF (nn : ℕ) (p : ℝ) (k : ℕ) : ℝ :=
  ↑(nn.choose k) * p ^ k * (1 - p) ^ (nn - k)

/-! ## Helper lemmas -/

/-- `fixedSizeRestrProb` is between 0 and 1. -/
lemma fixedSizeRestrProb_nonneg (event : Restriction n → Prop)
    [DecidablePred event] (k : ℕ) :
    0 ≤ fixedSizeRestrProb event k := by
  unfold fixedSizeRestrProb
  apply div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)

lemma fixedSizeRestrProb_le_one (event : Restriction n → Prop)
    [DecidablePred event] (k : ℕ) :
    fixedSizeRestrProb event k ≤ 1 := by
  unfold fixedSizeRestrProb
  rcases Nat.eq_zero_or_pos (fixedSizeRestrs n k).card with h | h
  · simp [h]
  · rw [div_le_one (Nat.cast_pos.mpr h)]
    exact Nat.cast_le.mpr (Finset.card_filter_le _ _)

/-- Binomial PMF is nonneg when `0 ≤ p ≤ 1`. -/
lemma binomialPMF_nonneg (p : ℝ) (hp : 0 ≤ p) (hp1 : p ≤ 1) (k : ℕ) :
    0 ≤ binomialPMF n p k := by
  unfold binomialPMF
  apply mul_nonneg
  apply mul_nonneg
  · exact Nat.cast_nonneg _
  · exact pow_nonneg hp _
  · exact pow_nonneg (sub_nonneg.mpr hp1) _

/-
Binomial PMF sums to 1 (the binomial theorem: `(p + (1-p))^n = 1`).
-/
lemma binomialPMF_sum_one (p : ℝ) (hp : 0 ≤ p) (hp1 : p ≤ 1) :
    ∑ k ∈ Finset.range (n + 1), binomialPMF n p k = 1 := by
  unfold binomialPMF;
  have := add_pow p ( 1 - p ) n;
  simpa [ mul_assoc, mul_comm, mul_left_comm ] using this.symm

/-! ## Decomposition of Bernoulli probability -/

/-
**Decomposition of Bernoulli probability by free-variable count.**
The Bernoulli(`p`) restriction probability decomposes as
`Pr_{R_p}[bad] = ∑_{k=0}^{n} Pr[Bin(n,p)=k] · Pr_{R_k}[bad]`,
because conditioning `R_p` on `|ρ⁻¹(⋆)| = k` yields exactly `R_k`.
-/
set_option maxHeartbeats 800000 in
lemma bernoulli_decompose (p : ℝ) (hp : 0 ≤ p) (hp1 : p ≤ 1)
    (event : Restriction n → Prop) [DecidablePred event] :
    bernoulliRestrProb p event =
    ∑ k ∈ Finset.range (n + 1),
      binomialPMF n p k * fixedSizeRestrProb event k := by
  have h_card_fixedSizeRestrs : ∀ k ≤ n, (fixedSizeRestrs n k).card = Nat.choose n k * 2 ^ (n - k) := by
    intro k hk;
    -- The set of restrictions with exactly k free variables is in bijection with the set of subsets of size k from the set of n variables.
    have h_bij : (fixedSizeRestrs n k).card = (Finset.powersetCard k (Finset.univ : Finset (Fin n))).card * 2 ^ (n - k) := by
      have h_bij : ∀ s : Finset (Fin n), s.card = k → (Finset.filter (fun ρ : Restriction n => ρ.freeVars = s) (Finset.univ : Finset (Restriction n))).card = 2 ^ (n - k) := by
        intro s hs_card
        have h_restrictions : (Finset.univ.filter (fun ρ : Restriction n => ρ.freeVars = s)).card = (Finset.univ.filter (fun ρ : Fin n → Option Bool => ∀ i, ρ i = if i ∈ s then none else some (ρ i).get!)).card := by
          refine' Finset.card_bij ( fun ρ _ => ρ ) _ _ _ <;> simp +decide [ Restriction.freeVars ];
          · intro ρ hρ i; by_cases hi : i ∈ s <;> simp_all +decide [ Finset.ext_iff ] ;
            cases h : ρ i <;> specialize hρ i <;> aesop;
          · grind;
        -- Each restriction with free variables exactly $s$ corresponds to a function from the complement of $s$ to $\{0, 1\}$.
        have h_restrictions_bij : (Finset.univ.filter (fun ρ : Fin n → Option Bool => ∀ i, ρ i = if i ∈ s then none else some (ρ i).get!)).card = (Finset.univ.filter (fun ρ : Fin n → Bool => ∀ i ∈ s, ρ i = false)).card := by
          refine' Finset.card_bij ( fun ρ _ => fun i => if i ∈ s then false else ( ρ i ).get! ) _ _ _ <;> simp +decide [ funext_iff ];
          · tauto;
          · grind;
          · intro b hb; use fun i => if i ∈ s then none else some ( b i ) ; aesop;
        have h_complement_card : (Finset.univ.filter (fun ρ : Fin n → Bool => ∀ i ∈ s, ρ i = false)).card = (Finset.univ.filter (fun ρ : {i : Fin n // i ∉ s} → Bool => True)).card := by
          refine' Finset.card_bij ( fun ρ hρ => fun i => ρ i ) _ _ _ <;> simp +decide [ Finset.mem_filter ];
          · intro a₁ ha₁ a₂ ha₂ h; ext i; by_cases hi : i ∈ s <;> simp_all +decide [ funext_iff ] ;
          · intro b; use fun i => if hi : i ∈ s then false else b ⟨ i, hi ⟩ ; aesop;
        simp_all +decide [ Finset.card_univ ];
      have h_bij : (fixedSizeRestrs n k).card = ∑ s ∈ Finset.powersetCard k (Finset.univ : Finset (Fin n)), (Finset.filter (fun ρ : Restriction n => ρ.freeVars = s) (Finset.univ : Finset (Restriction n))).card := by
        rw [ ← Finset.card_biUnion ];
        · congr with ρ ; simp +decide [ fixedSizeRestrs ];
        · exact fun s hs t ht hst => Finset.disjoint_left.mpr fun x hx hx' => hst <| by aesop;
      rw [ h_bij, Finset.sum_congr rfl fun s hs => ‹∀ s : Finset ( Fin n ), s.card = k → Finset.card { ρ : Restriction n | ρ.freeVars = s } = 2 ^ ( n - k ) › s <| Finset.mem_powersetCard.mp hs |>.2, Finset.sum_const, smul_eq_mul, mul_comm ];
    rw [ h_bij, Finset.card_powersetCard, Finset.card_fin ];
  have h_decomp : bernoulliRestrProb p event = ∑ k ∈ Finset.range (n + 1), ∑ ρ ∈ fixedSizeRestrs n k, (bernoulliRestrWeight p ρ * if event ρ then 1 else 0) := by
    rw [ Finset.sum_sigma' ];
    refine' Finset.sum_bij ( fun x hx => ⟨ x.freeVars.card, x ⟩ ) _ _ _ _ <;> simp +decide [ fixedSizeRestrs ];
    · exact fun ρ => by
        have h1 : ρ.freeVars.card ≤ (Finset.univ : Finset (Fin n)).card := Finset.card_le_univ _
        have h2 : (Finset.univ : Finset (Fin n)).card = n := by
          rw [Finset.card_univ, Fintype.card_fin]
        omega
    · exact fun b hb₁ hb₂ => ⟨ b.2, by aesop ⟩;
  have h_decomp : ∀ k ≤ n, ∑ ρ ∈ fixedSizeRestrs n k, (bernoulliRestrWeight p ρ * if event ρ then 1 else 0) = (binomialPMF n p k) * ((fixedSizeRestrs n k).filter (fun ρ => event ρ)).card / (fixedSizeRestrs n k).card := by
    intro k hk
    have h_decomp : ∀ ρ ∈ fixedSizeRestrs n k, bernoulliRestrWeight p ρ = p ^ k * ((1 - p) / 2) ^ (n - k) := by
      unfold fixedSizeRestrs at *; aesop;
    rw [ Finset.sum_congr rfl fun x hx => by rw [ h_decomp x hx ] ]
    simp_rw [ show ∀ x : Restriction n, p ^ k * ((1 - p) / 2) ^ (n - k) * (if event x then 1 else 0) =
        if event x then p ^ k * ((1 - p) / 2) ^ (n - k) else 0 from fun x => by split_ifs <;> ring ]
    rw [ Finset.sum_ite, Finset.sum_const_zero, add_zero, Finset.sum_const, nsmul_eq_mul,
         h_card_fixedSizeRestrs k hk ]
    have hdenom : (↑(Nat.choose n k * 2 ^ (n - k)) : ℝ) ≠ 0 := by
      exact_mod_cast (Nat.mul_pos (Nat.choose_pos hk) (pow_pos (by norm_num : (0:ℕ) < 2) (n - k))).ne'
    rw [ eq_div_iff hdenom ]
    simp only [ binomialPMF ]
    push_cast
    rw [ div_pow ]
    have h2pow_ne : (2 : ℝ) ^ (n - k) ≠ 0 := by positivity
    field_simp [ h2pow_ne ]
  convert ‹bernoulliRestrProb p event = ∑ k ∈ Finset.range ( n + 1 ), ∑ ρ ∈ fixedSizeRestrs n k, bernoulliRestrWeight p ρ * if event ρ then 1 else 0› using 2;
  rw [ h_decomp _ ( Finset.mem_range_succ_iff.mp ‹_› ), fixedSizeRestrProb ] ; ring

/-! ## Chernoff bound -/

/-
**Multiplicative Chernoff bound for the binomial distribution.**
For `K ~ Bin(n, p)`, we have `Pr[K > 2np] ≤ e^{-np/3}`.
This follows from the standard Chernoff bound with `δ = 1`.
-/
lemma chernoff_binomial_upper_tail (nn : ℕ) (p : ℝ) (hp : 0 < p) (hp1 : p ≤ 1) :
    ∑ k ∈ (Finset.range (nn + 1)).filter (fun k : ℕ => (↑k : ℝ) > 2 * ↑nn * p),
      binomialPMF nn p k ≤ Real.exp (-(↑nn * p / 3)) := by
  by_cases h_cases : p ≤ 0.5;
  · -- Using the Chernoff bound, we have:
    have h_chernoff : (∑ k ∈ Finset.range (nn + 1), (nn.choose k) * p^k * (1 - p)^(nn - k) * Real.exp ((k - 2 * nn * p) * Real.log 2)) ≤ Real.exp (nn * p * (Real.exp (Real.log 2) - 1) - 2 * nn * p * Real.log 2) := by
      have h_chernoff : (∑ k ∈ Finset.range (nn + 1), (nn.choose k) * p^k * (1 - p)^(nn - k) * Real.exp (k * Real.log 2)) ≤ Real.exp (nn * p * (Real.exp (Real.log 2) - 1)) := by
        have h_chernoff : (∑ k ∈ Finset.range (nn + 1), (nn.choose k) * p^k * (1 - p)^(nn - k) * Real.exp (k * Real.log 2)) = (p * Real.exp (Real.log 2) + (1 - p)) ^ nn := by
          rw [ add_pow ];
          exact Finset.sum_congr rfl fun x hx => by rw [ mul_pow, ← Real.exp_nat_mul ] ; ring;
        rw [ h_chernoff, ← Real.rpow_natCast, Real.rpow_def_of_pos ( by nlinarith [ Real.add_one_le_exp ( Real.log 2 ), Real.log_pos one_lt_two ] ) ] ; ring_nf ; norm_num;
        exact le_trans ( mul_le_mul_of_nonneg_right ( Real.log_le_sub_one_of_pos ( by nlinarith [ Real.add_one_le_exp ( Real.log 2 ), Real.log_pos one_lt_two ] ) ) ( Nat.cast_nonneg _ ) ) ( by nlinarith [ Real.add_one_le_exp ( Real.log 2 ), Real.log_pos one_lt_two ] );
      convert mul_le_mul_of_nonneg_right h_chernoff ( Real.exp_nonneg ( -2 * nn * p * Real.log 2 ) ) using 1 <;> norm_num [ sub_mul, Real.exp_add, Real.exp_sub ] ; ring;
      · rw [ Finset.sum_mul _ _ _ ] ; congr ; ext ; rw [ ← Real.exp_neg ] ; ring;
      · rw [ div_eq_mul_inv, Real.exp_neg ];
    -- Simplify the exponent in the Chernoff bound.
    have h_exp_simplified : Real.exp (nn * p * (Real.exp (Real.log 2) - 1) - 2 * nn * p * Real.log 2) ≤ Real.exp (-nn * p / 3) := by
      norm_num [ Real.exp_log ] at *;
      have := Real.log_two_gt_d9 ; norm_num at this ; nlinarith [ mul_nonneg ( Nat.cast_nonneg nn ) hp.le ];
    -- Apply the Chernoff bound to the sum.
    have h_sum_bound : (∑ k ∈ Finset.range (nn + 1), (if k > 2 * nn * p then (nn.choose k) * p^k * (1 - p)^(nn - k) else 0)) ≤ Real.exp (-nn * p / 3) := by
      refine le_trans ?_ ( h_chernoff.trans h_exp_simplified );
      gcongr;
      split_ifs;
      · exact le_mul_of_one_le_right ( mul_nonneg ( mul_nonneg ( Nat.cast_nonneg _ ) ( pow_nonneg hp.le _ ) ) ( pow_nonneg ( sub_nonneg.mpr hp1 ) _ ) ) ( Real.one_le_exp ( mul_nonneg ( sub_nonneg.mpr <| le_of_lt ‹_› ) ( Real.log_nonneg one_le_two ) ) );
      · exact mul_nonneg ( mul_nonneg ( mul_nonneg ( Nat.cast_nonneg _ ) ( pow_nonneg hp.le _ ) ) ( pow_nonneg ( sub_nonneg.mpr hp1 ) _ ) ) ( Real.exp_nonneg _ );
    convert h_sum_bound using 1 <;> norm_num [ Finset.sum_ite, binomialPMF ] ; ring;
  · rcases eq_or_ne nn 0 <;> simp_all +decide [ binomialPMF ];
    · norm_num [ Finset.sum_filter ];
    · have hempty : (Finset.range (nn + 1)).filter (fun k : ℕ => (↑k : ℝ) > 2 * ↑nn * p) = ∅ := by
        ext k
        simp only [Finset.mem_filter, Finset.mem_range, Finset.not_mem_empty, iff_false, not_and]
        intro hk
        push_neg
        have hk_le : (k : ℝ) ≤ ↑nn := by exact_mod_cast Nat.lt_succ_iff.mp hk
        have hnn_pos : (0 : ℝ) < ↑nn := by
          have : 0 < nn := by omega
          exact_mod_cast this
        have hp_gt : (0.5 : ℝ) < p := by linarith
        nlinarith
      rw [hempty, Finset.sum_empty]; exact Real.exp_nonneg _

/-! ## Main theorem: exact cost -/

/-
**Bernoulli restriction cost theorem (exact version).**

If `Pr_{R_k}[bad] ≤ (5kw/n)^s` for every `k`, then
`Pr_{R_p}[bad] ≤ (10pw)^s + e^{-np/3}`.
-/
theorem bernoulli_restriction_cost
    (n_pos : 0 < n) (p : ℝ) (hp : 0 < p) (hp1 : p ≤ 1)
    (w s : ℕ) (hw : 0 < w) (_hs : 0 < s)
    (event : Restriction n → Prop) [DecidablePred event]
    (h_fixed : ∀ k : ℕ, k ≤ n →
      fixedSizeRestrProb event k ≤ (5 * ↑k * ↑w / ↑n) ^ s) :
    bernoulliRestrProb p event ≤
      (10 * p * ↑w) ^ s + Real.exp (-(↑n * p / 3)) := by
  -- Apply h_bound to each term in the split sum.
  have h_split : bernoulliRestrProb p event ≤ (∑ k ∈ Finset.range (n + 1), if (k : ℝ) ≤ 2 * (n : ℝ) * p then binomialPMF n p k * ((10 * p * w) ^ s) else 0) + (∑ k ∈ Finset.range (n + 1), if (k : ℝ) > 2 * (n : ℝ) * p then binomialPMF n p k else 0) := by
    rw [ ← Finset.sum_add_distrib, bernoulli_decompose p hp.le hp1 event ];
    gcongr;
    split_ifs <;> simp_all +decide [ mul_assoc, mul_comm, mul_left_comm ];
    · linarith;
    · refine' mul_le_mul_of_nonneg_left _ ( binomialPMF_nonneg p hp.le hp1 _ );
      refine le_trans ( h_fixed _ (by omega) ) ?_;
      exact pow_le_pow_left₀ ( by positivity ) ( by rw [ div_le_iff₀ ( by positivity ) ] ; nlinarith [ ( by norm_cast : ( 1 :ℝ ) ≤ w ) ] ) _;
    · exact mul_le_of_le_one_right ( binomialPMF_nonneg p hp.le hp1 _ ) ( fixedSizeRestrProb_le_one _ _ );
  refine le_trans h_split ?_;
  refine' add_le_add _ _;
  · -- Factor out $(10 * p * w) ^ s$ from the sum.
    suffices h_factor : (∑ k ∈ Finset.range (n + 1), if (k : ℝ) ≤ 2 * (n : ℝ) * p then binomialPMF n p k else 0) ≤ 1 by
      convert mul_le_mul_of_nonneg_right h_factor ( pow_nonneg ( show 0 ≤ 10 * p * w by positivity ) s ) using 1 <;> norm_num [ Finset.sum_ite ] ; ring;
      simp +decide only [mul_comm, mul_assoc, Finset.mul_sum _ _ _];
    refine' le_trans ( Finset.sum_le_sum fun _ _ => _ ) ( binomialPMF_sum_one p hp.le hp1 |> le_of_eq );
    split_ifs <;> norm_num [ binomialPMF_nonneg p hp.le hp1 ];
  · convert chernoff_binomial_upper_tail n p hp hp1 using 1;
    rw [ Finset.sum_filter ]

/-! ## Asymptotic version -/

/-
**Exponential decay.** For any `ε > 0` and `p > 0`, the tail bound
    `e^{-np/3}` eventually becomes smaller than `ε`.
-/
lemma exp_neg_eventually_small (p : ℝ) (hp : 0 < p) (ε : ℝ) (hε : 0 < ε) :
    ∃ N : ℕ, ∀ m : ℕ, N ≤ m →
      Real.exp (-(↑m * p / 3)) < ε := by
  simpa [ neg_div ] using ( Real.tendsto_exp_atBot.comp <| Filter.tendsto_neg_atTop_atBot.comp <| Filter.Tendsto.atTop_div_const ( by positivity ) <| tendsto_natCast_atTop_atTop.atTop_mul_const hp ) |> fun h => h.eventually ( gt_mem_nhds hε ) |> fun h => Filter.eventually_atTop.mp h |> fun ⟨ N, hN ⟩ => ⟨ N, fun m hm => hN m hm ⟩

/-- **Bernoulli restriction cost theorem (asymptotic version).**

For any `ε > 0`, there exists `N` such that for all `n ≥ N`,
if `Pr_{R_k}[bad] ≤ (5kw/n)^s` for every `k ≤ n`, then
`Pr_{R_p}[bad] ≤ (10pw)^s + ε`.

Asymptotically, the cost of switching from the fixed-size
model `R_k` to the Bernoulli model `R_p` vanishes entirely, and the
leading-order bound `(10pw)^s` is all that remains. -/
theorem bernoulli_restriction_asymptotic
    (p : ℝ) (hp : 0 < p) (hp1 : p ≤ 1)
    (w s : ℕ) (hw : 0 < w) (hs : 0 < s)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ N : ℕ, ∀ nn : ℕ, N ≤ nn → 0 < nn →
    ∀ (event : Restriction nn → Prop) [DecidablePred event],
    (∀ k : ℕ, k ≤ nn →
      fixedSizeRestrProb event k ≤ (5 * ↑k * ↑w / ↑nn) ^ s) →
    bernoulliRestrProb p event ≤ (10 * p * ↑w) ^ s + ε := by
  obtain ⟨N, hN⟩ := exp_neg_eventually_small p hp ε hε
  exact ⟨N, fun nn hn hn_pos event _ h_fixed => by
    calc bernoulliRestrProb p event
        ≤ (10 * p * ↑w) ^ s + Real.exp (-(↑nn * p / 3)) :=
          bernoulli_restriction_cost hn_pos p hp hp1 w s hw hs event h_fixed
      _ ≤ (10 * p * ↑w) ^ s + ε := by linarith [hN nn hn]⟩

end BernoulliCost

end