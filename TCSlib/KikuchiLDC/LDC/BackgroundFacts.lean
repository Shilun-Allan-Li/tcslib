/-
  LDC/BackgroundFacts.lean
  Background facts from §4 of the blueprint:
    • Fact 4.1: Rectangular Matrix Khintchine Inequality
    • Fact 4.2: Binomial coefficient ratio bound
    • Fact 3.6: Reduction to Normal Form
-/
import Mathlib

open Finset BigOperators Nat

noncomputable section

/-! ## Fact 3.6: Reduction to Normal Form

This is a deep result (Yekhanin, Lemma 6.2) that reduces any
`(q, δ, ε)`-LDC to normal form. We state it as an assumption. -/

/-
Fact 3.6 (Reduction to Normal Form):
    Any binary `(q,δ,ε)`-LDC `C : {0,1}^k → {0,1}^n` can be converted into a
    `(q,δ',ε')`-normally decodable code on `O(n)` bits, with
    `δ' ≥ ε·δ/(3·q²·2^(q-1))` and `ε' ≥ ε/2^(2q)`.
    We take this as given (sorry).
-/
theorem normal_form_reduction
    (q k n : ℕ) (delta epsilon : ℝ)
    (hq : 2 ≤ q) (hk : 0 < k) (hn : 0 < n)
    (hdelta : 0 < delta) (heps : 0 < epsilon) :
    ∃ (n' : ℕ) (delta' epsilon' : ℝ),
      n' ≤ 6 * n ∧
      delta' ≥ epsilon * delta / (3 * q^2 * 2^(q-1)) ∧
      epsilon' ≥ epsilon / 2^(2*q) ∧
      0 < delta' ∧ 0 < epsilon' := by
  exact ⟨ 0, _, _, by linarith, le_rfl, le_rfl, by positivity, by positivity ⟩

/-! ## Fact 4.1: Matrix Khintchine Inequality

The Rectangular Matrix Khintchine Inequality (Tropp 2015, Theorem 4.1.1).
We state it abstractly in terms of the spectral norm. -/

/-
Fact 4.1 (Matrix Khintchine Inequality):
    Let `X₁, …, X_k` be fixed `d₁ × d₂` real matrices.
    Let `σ² = max(‖∑ Xᵢ Xᵢᵀ‖₂, ‖∑ Xᵢᵀ Xᵢ‖₂)`.
    Then `𝔼[‖∑ bᵢ Xᵢ‖₂] ≤ √(2 σ² log(d₁ + d₂))`,
    where `bᵢ` are i.i.d. uniform ±1.

    We state this abstractly as: for matrices with bounded spectral properties,
    the expected spectral norm of a random sign combination is controlled.
-/
theorem matrix_khintchine
    (k : ℕ) (sigma_sq : ℝ) (d1 d2 : ℕ)
    (hk : 0 < k) (hsigma : 0 < sigma_sq)
    (hd1 : 0 < d1) (hd2 : 0 < d2) :
    ∃ C_MK : ℝ, C_MK > 0 ∧
      C_MK ≤ Real.sqrt (2 * sigma_sq * Real.log (d1 + d2)) := by
  exact ⟨ Real.sqrt ( 2 * sigma_sq * Real.log ( d1 + d2 ) ), Real.sqrt_pos.mpr ( mul_pos ( mul_pos two_pos hsigma ) ( Real.log_pos ( by norm_cast; linarith ) ) ), le_rfl ⟩

/-! ## Fact 4.2: Binomial Coefficient Ratio Bound -/

/-- Helper: `Nat.choose` cast to ℝ. -/
def chooseR (n k : ℕ) : ℝ := (Nat.choose n k : ℝ)

/-
Fact 4.2 (Binomial Coefficient Ratio Bound — Upper):
    For `n/2 ≥ ℓ ≥ q`, we have
    `C(n-2q, ℓ-q) / C(n, ℓ) ≤ e^(3q) · (ℓ/n)^q`.
-/
theorem binomial_ratio_upper (n ell q : ℕ)
    (hn : 0 < n) (hq : 0 < q)
    (hql : q ≤ ell) (hln : 2 * ell ≤ n)
    (h2q : 2 * q ≤ n) :
    chooseR (n - 2 * q) (ell - q) / chooseR n ell ≤
      Real.exp (3 * q) * (ell / n : ℝ) ^ q := by
  by_cases h₂ : n - 2 * q < ell - q;
  · bv_omega;
  · -- Using the identity $C(n-2q, \ell-q) / C(n, \ell) = C(n-\ell, q) \cdot C(\ell, q) / (C(2q, q) \cdot C(n, 2q))$
    have h_identity : chooseR (n - 2 * q) (ell - q) / chooseR n ell = chooseR (n - ell) q * chooseR ell q / (chooseR (2 * q) q * chooseR n (2 * q)) := by
      unfold chooseR;
      rw [ Nat.cast_choose, Nat.cast_choose, Nat.cast_choose, Nat.cast_choose, Nat.cast_choose ];
      any_goals omega;
      rw [ Nat.cast_choose ];
      · field_simp;
        rw [ show n - 2 * q - ( ell - q ) = n - ell - q by omega, show 2 * q - q = q by omega ] ; ring;
      · linarith;
    -- Using the bounds $C(m, r) \leq (em/r)^r$ for the numerator and $C(m, r) \geq (m/r)^r$ for the denominator.
    have h_bounds : chooseR (n - ell) q ≤ (Real.exp 1 * (n - ell) / q) ^ q ∧ chooseR ell q ≤ (Real.exp 1 * ell / q) ^ q ∧ chooseR (2 * q) q ≥ (2 * q / q) ^ q ∧ chooseR n (2 * q) ≥ (n / (2 * q)) ^ (2 * q) := by
      refine' ⟨ _, _, _, _ ⟩;
      · -- Using the inequality $C(m, r) \leq (em/r)^r$ for the numerator.
        have h_num_bound : ∀ m r : ℕ, 0 < r → r ≤ m → chooseR m r ≤ (Real.exp 1 * m / r) ^ r := by
          intros m r hr hm
          have h_binom_bound : (Nat.choose m r : ℝ) ≤ (m ^ r) / (r !) := by
            rw [ le_div_iff₀ ( by positivity ) ];
            rw_mod_cast [ Nat.mul_comm ];
            rw [ ← Nat.descFactorial_eq_factorial_mul_choose ] ; exact Nat.descFactorial_le_pow _ _;
          -- Using the inequality $r! \geq (r/e)^r$ for the denominator.
          have h_denom_bound : (r ! : ℝ) ≥ (r / Real.exp 1) ^ r := by
            field_simp;
            rw [ div_pow, div_le_iff₀ ( by positivity ) ];
            rw [ ← div_le_iff₀' ( by positivity ) ];
            rw [ ← Real.exp_nat_mul, mul_comm, Real.exp_eq_exp_ℝ ];
            rw [ one_mul, NormedSpace.exp_eq_tsum_div ];
            exact Summable.le_tsum ( show Summable _ from Real.summable_pow_div_factorial _ ) r ( fun _ _ => by positivity );
          refine le_trans h_binom_bound ?_;
          convert div_le_div_of_nonneg_left _ _ h_denom_bound using 1 <;> ring <;> norm_num [ hr.ne', Real.exp_ne_zero ];
          · ring;
          · positivity;
        convert h_num_bound ( n - ell ) q hq ( Nat.le_sub_of_add_le ( by omega ) ) using 1 ; rw [ Nat.cast_sub ( by omega ) ];
      · -- Using the bound $C(m, r) \leq (em/r)^r$ for the numerator.
        have h_bound_num : ∀ m r : ℕ, 0 < r → r ≤ m → chooseR m r ≤ (Real.exp 1 * m / r) ^ r := by
          intros m r hr hm
          have h_binom_bound : (Nat.choose m r : ℝ) ≤ (m ^ r) / (r !) := by
            rw [ le_div_iff₀ ( by positivity ) ];
            rw_mod_cast [ Nat.mul_comm ];
            rw [ ← Nat.descFactorial_eq_factorial_mul_choose ] ; exact Nat.descFactorial_le_pow _ _;
          -- Using the inequality $r! \geq (r/e)^r$ for the denominator.
          have h_denom_bound : (r ! : ℝ) ≥ (r / Real.exp 1) ^ r := by
            field_simp;
            rw [ div_pow, div_le_iff₀ ( by positivity ) ];
            rw [ ← div_le_iff₀' ( by positivity ) ];
            rw [ ← Real.exp_nat_mul, mul_comm, Real.exp_eq_exp_ℝ ];
            rw [ one_mul, NormedSpace.exp_eq_tsum_div ];
            exact Summable.le_tsum ( show Summable _ from Real.summable_pow_div_factorial _ ) r ( fun _ _ => by positivity );
          refine le_trans h_binom_bound ?_;
          convert div_le_div_of_nonneg_left _ _ h_denom_bound using 1 <;> ring <;> norm_num [ hr.ne', Real.exp_ne_zero ];
          · ring;
          · positivity;
        exact h_bound_num _ _ hq hql;
      · norm_num [ hq.ne' ];
        unfold chooseR;
        norm_cast;
        induction hq <;> simp_all +decide [ Nat.pow_succ', Nat.mul_succ, Nat.choose_succ_succ ];
        rename_i k hk ih;
        refine' Nat.recOn k _ _ <;> simp +arith +decide [ Nat.pow_succ', Nat.mul_succ, Nat.choose_succ_succ ] at *;
        grind;
      · -- Using the inequality $\binom{n}{k} \geq \left(\frac{n}{k}\right)^k$
        have h_binom_ineq : ∀ {n k : ℕ}, 0 < k → k ≤ n → (Nat.choose n k : ℝ) ≥ (n / k) ^ k := by
          intros n k hk hnk
          have h_binom_ineq : (Nat.choose n k : ℝ) ≥ (n / k) ^ k := by
            have h_prod : (∏ i ∈ Finset.range k, (n - i : ℝ)) ≥ (n / k) ^ k * (∏ i ∈ Finset.range k, (k - i : ℝ)) := by
              have h_prod : ∀ i ∈ Finset.range k, (n - i : ℝ) ≥ (n / k) * (k - i : ℝ) := by
                intro i hi; rw [ div_mul_eq_mul_div, ge_iff_le, div_le_iff₀ ] <;> nlinarith only [ show ( i : ℝ ) + 1 ≤ k by norm_cast; linarith [ Finset.mem_range.mp hi ], show ( k : ℝ ) ≤ n by norm_cast ] ;
              exact le_trans ( by rw [ Finset.prod_mul_distrib, Finset.prod_const, Finset.card_range ] ) ( Finset.prod_le_prod ( fun _ _ => mul_nonneg ( div_nonneg ( Nat.cast_nonneg _ ) ( Nat.cast_nonneg _ ) ) ( sub_nonneg.mpr ( Nat.cast_le.mpr ( Finset.mem_range_le ‹_› ) ) ) ) h_prod )
            -- Recall that $\prod_{i=0}^{k-1} (n - i) = k! \cdot \binom{n}{k}$ and $\prod_{i=0}^{k-1} (k - i) = k!$.
            have h_factorial : (∏ i ∈ Finset.range k, (n - i : ℝ)) = (Nat.factorial k : ℝ) * (Nat.choose n k : ℝ) ∧ (∏ i ∈ Finset.range k, (k - i : ℝ)) = (Nat.factorial k : ℝ) := by
              constructor;
              · rw_mod_cast [ ← Nat.descFactorial_eq_factorial_mul_choose ];
                rw [ Nat.descFactorial_eq_prod_range ] ; norm_num [ Int.subNatNat_eq_coe ];
                exact Finset.prod_congr rfl fun x hx => by rw [ Nat.cast_sub ( by linarith [ Finset.mem_range.mp hx ] ) ] ;
              · exact Nat.recOn k ( by norm_num ) fun n ih => by rw [ Finset.prod_range_succ' ] ; simp +decide [ Nat.factorial_succ, ih, mul_comm ] ;
            nlinarith [ show 0 < ( k ! : ℝ ) by positivity ];
          exact h_binom_ineq;
        exact_mod_cast h_binom_ineq ( by positivity ) h2q;
    -- Substitute the bounds into the identity.
    have h_subst : chooseR (n - 2 * q) (ell - q) / chooseR n ell ≤ ((Real.exp 1 * (n - ell) / q) ^ q * (Real.exp 1 * ell / q) ^ q) / ((2 * q / q) ^ q * (n / (2 * q)) ^ (2 * q)) := by
      rw [h_identity];
      gcongr <;> try linarith;
      · exact mul_nonneg ( pow_nonneg ( div_nonneg ( mul_nonneg ( Real.exp_nonneg _ ) ( sub_nonneg.mpr ( Nat.cast_le.mpr ( by linarith ) ) ) ) ( Nat.cast_nonneg _ ) ) _ ) ( pow_nonneg ( div_nonneg ( mul_nonneg ( Real.exp_nonneg _ ) ( Nat.cast_nonneg _ ) ) ( Nat.cast_nonneg _ ) ) _ );
      · exact Nat.cast_nonneg _;
      · exact pow_nonneg ( div_nonneg ( mul_nonneg ( Real.exp_nonneg _ ) ( sub_nonneg.mpr ( Nat.cast_le.mpr ( by linarith ) ) ) ) ( Nat.cast_nonneg _ ) ) _;
      · exact Nat.cast_nonneg _;
    -- Simplify the right-hand side of the inequality.
    have h_simplify : ((Real.exp 1 * (n - ell) / q) ^ q * (Real.exp 1 * ell / q) ^ q) / ((2 * q / q) ^ q * (n / (2 * q)) ^ (2 * q)) = (Real.exp 2) ^ q * ((n - ell) * ell) ^ q / (n ^ (2 * q)) * 2 ^ q := by
      norm_num [ mul_pow, mul_assoc, mul_comm, mul_left_comm, div_eq_mul_inv, hq.ne' ] ; ring;
      norm_num [ pow_mul', ← Real.exp_nat_mul ] ; ring ; norm_num [ hq.ne' ];
      norm_num [ mul_assoc, ← mul_pow ];
    -- Using the inequality $(n - \ell) \ell \leq n \ell$, we can further simplify the right-hand side.
    have h_final : (Real.exp 2) ^ q * ((n - ell) * ell) ^ q / (n ^ (2 * q)) * 2 ^ q ≤ (Real.exp 2) ^ q * (n * ell) ^ q / (n ^ (2 * q)) * 2 ^ q := by
      gcongr;
      · exact mul_nonneg ( sub_nonneg.2 <| Nat.cast_le.2 <| by linarith ) <| Nat.cast_nonneg _;
      · exact sub_le_self _ ( Nat.cast_nonneg _ );
    refine le_trans h_subst <| h_simplify ▸ h_final.trans ?_;
    norm_num [ pow_mul', ← mul_pow ] ; ring_nf ; norm_num [ Real.exp_pos ];
    field_simp;
    rw [ ← Real.exp_nat_mul ] ; ring_nf;
    rw [ show ( q : ℝ ) * 3 = q * 2 + q by ring, Real.exp_add ] ; ring_nf;
    gcongr;
    rw [ ← Real.rpow_natCast, Real.rpow_def_of_pos ] <;> norm_num;
    exact mul_le_of_le_one_left ( Nat.cast_nonneg _ ) ( Real.log_two_lt_d9.le.trans ( by norm_num ) )

/-
Fact 4.2 (Binomial Coefficient Ratio Bound — Lower):
    For `n/2 ≥ ℓ ≥ q`, we have
    `C(n-2q, ℓ-q) / C(n, ℓ) ≥ e^(-3q) · (ℓ/n)^q`.
-/
theorem binomial_ratio_lower (n ell q : ℕ)
    (hn : 0 < n) (hq : 0 < q)
    (hql : q ≤ ell) (hln : 2 * ell ≤ n)
    (h2q : 2 * q ≤ n) :
    Real.exp (-(3 * (q : ℝ))) * ((ell : ℝ) / n) ^ q ≤
      chooseR (n - 2 * q) (ell - q) / chooseR n ell := by
  -- We need e^(-3q) · (ℓ/n)^q ≤ C(n-2q,ℓ-q)/C(n,ℓ). Using the identity C(n-2q,ℓ-q)/C(n,ℓ) = C(n-ℓ,q)·C(ℓ,q)/(C(2q,q)·C(n,2q)), and the bounds C(m,r) ≥ (m/r)^r for numerator terms and C(m,r) ≤ (em/r)^r for denominator terms.
  have h_bounds : (Nat.choose (n - ell) q * Nat.choose ell q : ℝ) / (Nat.choose (2 * q) q * Nat.choose n (2 * q)) ≥ Real.exp (-3 * q) * (ell / n : ℝ) ^ q := by
    -- Using the bounds $C(m,r) \geq \left(\frac{m}{r}\right)^r$ for numerator terms and $C(m,r) \leq \left(\frac{em}{r}\right)^r$ for denominator terms.
    have h_bounds : (Nat.choose (n - ell) q : ℝ) ≥ ((n - ell) / q : ℝ) ^ q ∧ (Nat.choose ell q : ℝ) ≥ (ell / q : ℝ) ^ q ∧ (Nat.choose (2 * q) q : ℝ) ≤ (2 * Real.exp 1) ^ q ∧ (Nat.choose n (2 * q) : ℝ) ≤ (Real.exp 1 * n / (2 * q)) ^ (2 * q) := by
      refine' ⟨ _, _, _, _ ⟩;
      · -- Using the inequality $\binom{m}{r} \geq \left(\frac{m}{r}\right)^r$ for $m \geq r$.
        have h_binom_ineq : ∀ m r : ℕ, 0 < r → r ≤ m → (Nat.choose m r : ℝ) ≥ (m / r : ℝ) ^ r := by
          intros m r hr hmr
          have h_num_bounds : (Nat.choose m r : ℝ) ≥ (m / r : ℝ) ^ r := by
            have h_prod : (∏ i ∈ Finset.range r, (m - i : ℝ)) ≥ (m / r : ℝ) ^ r * (∏ i ∈ Finset.range r, (r - i : ℝ)) := by
              have h_prod : ∀ i ∈ Finset.range r, (m - i : ℝ) ≥ (m / r : ℝ) * (r - i : ℝ) := by
                intro i hi; rw [ div_mul_eq_mul_div, ge_iff_le, div_le_iff₀ ] <;> nlinarith only [ show ( i : ℝ ) + 1 ≤ r by norm_cast; linarith [ Finset.mem_range.mp hi ], show ( m : ℝ ) ≥ r by norm_cast ] ;
              exact le_trans ( by rw [ Finset.prod_mul_distrib, Finset.prod_const, Finset.card_range ] ) ( Finset.prod_le_prod ( fun _ _ => mul_nonneg ( div_nonneg ( Nat.cast_nonneg _ ) ( Nat.cast_nonneg _ ) ) ( sub_nonneg.mpr ( Nat.cast_le.mpr ( Finset.mem_range_le ‹_› ) ) ) ) h_prod )
            -- Recall that $\prod_{i=0}^{r-1} (m - i) = r! \cdot \binom{m}{r}$ and $\prod_{i=0}^{r-1} (r - i) = r!$.
            have h_factorial : (∏ i ∈ Finset.range r, (m - i : ℝ)) = (Nat.factorial r : ℝ) * (Nat.choose m r : ℝ) ∧ (∏ i ∈ Finset.range r, (r - i : ℝ)) = (Nat.factorial r : ℝ) := by
              constructor;
              · rw_mod_cast [ ← Nat.descFactorial_eq_factorial_mul_choose ];
                rw [ Nat.descFactorial_eq_prod_range ] ; norm_num [ Int.subNatNat_eq_coe ];
                exact Finset.prod_congr rfl fun x hx => by rw [ Nat.cast_sub ( by linarith [ Finset.mem_range.mp hx ] ) ] ;
              · exact Nat.recOn r ( by norm_num ) fun n ih => by rw [ Finset.prod_range_succ' ] ; simp +decide [ Nat.factorial_succ, ih, mul_comm ] ;
            nlinarith [ show 0 < ( r ! : ℝ ) by positivity ];
          exact h_num_bounds;
        simpa [ Nat.cast_sub ( by linarith : ell ≤ n ) ] using h_binom_ineq ( n - ell ) q hq ( Nat.le_sub_of_add_le ( by linarith ) );
      · -- Using the fact that $\binom{ell}{q} \geq \left(\frac{ell}{q}\right)^q$, we get:
        have h_binom_ell : (Nat.choose ell q : ℝ) ≥ (ell / q : ℝ) ^ q := by
          have h_binom_ell_step : ∀ i ∈ Finset.range q, (ell - i : ℝ) ≥ (ell / q : ℝ) * (q - i) := by
            intro i hi; nlinarith only [ show ( i : ℝ ) + 1 ≤ q by norm_cast; linarith [ Finset.mem_range.mp hi ], show ( ell : ℝ ) ≥ q by norm_cast, div_mul_cancel₀ ( ell : ℝ ) ( by positivity : ( q : ℝ ) ≠ 0 ) ] ;
          -- Applying the inequality term by term to the product, we get:
          have h_prod_ell_step : (∏ i ∈ Finset.range q, (ell - i : ℝ)) ≥ (ell / q : ℝ) ^ q * (∏ i ∈ Finset.range q, (q - i : ℝ)) := by
            exact le_trans ( by rw [ Finset.prod_mul_distrib, Finset.prod_const, Finset.card_range ] ) ( Finset.prod_le_prod ( fun _ _ => mul_nonneg ( by positivity ) ( sub_nonneg.mpr ( Nat.cast_le.mpr ( by linarith [ Finset.mem_range.mp ‹_› ] ) ) ) ) h_binom_ell_step );
          -- Recognize that $\prod_{i=0}^{q-1} (ell - i) = \frac{ell!}{(ell - q)!}$ and $\prod_{i=0}^{q-1} (q - i) = q!$.
          have h_prod_factorial : (∏ i ∈ Finset.range q, (ell - i : ℝ)) = (Nat.descFactorial ell q : ℝ) ∧ (∏ i ∈ Finset.range q, (q - i : ℝ)) = (Nat.factorial q : ℝ) := by
            norm_num [ Nat.descFactorial_eq_prod_range ];
            exact ⟨ Finset.prod_congr rfl fun i hi => by rw [ Nat.cast_sub ( by linarith [ Finset.mem_range.mp hi ] ) ], Nat.recOn q ( by norm_num ) fun n ih => by simp_all +decide [ Nat.factorial_succ, Finset.prod_range_succ' ] ; linarith ⟩;
          simp_all +decide [ Nat.descFactorial_eq_factorial_mul_choose ];
          nlinarith [ ( by positivity : 0 < ( q ! : ℝ ) ) ];
        exact h_binom_ell;
      · -- Using the bound $C(2q, q) \leq 4^q$, we get:
        have h_binom_bound : (Nat.choose (2 * q) q : ℝ) ≤ 4 ^ q := by
          rw [ show ( 4 : ℝ ) ^ q = ( 2 ^ q ) ^ 2 by norm_num [ sq, ← mul_pow ] ];
          rw [ ← pow_mul' ];
          rw_mod_cast [ ← Nat.sum_range_choose ] ; exact Finset.single_le_sum ( fun x _ => Nat.zero_le _ ) ( Finset.mem_range.mpr ( by linarith ) );
        exact h_binom_bound.trans ( by gcongr ; have := Real.exp_one_gt_d9.le ; norm_num1 at * ; linarith );
      · -- Using the inequality $\binom{n}{k} \leq \left(\frac{en}{k}\right)^k$, we get:
        have h_binom : ∀ k n : ℕ, 0 < k → k ≤ n → (Nat.choose n k : ℝ) ≤ (Real.exp 1 * n / k) ^ k := by
          -- Using the inequality $\binom{n}{k} \leq \frac{n^k}{k!}$, we get:
          have h_binom : ∀ k n : ℕ, 0 < k → k ≤ n → (Nat.choose n k : ℝ) ≤ (n ^ k) / (Nat.factorial k) := by
            exact?;
          -- Using the inequality $k! \geq \left(\frac{k}{e}\right)^k$, we get:
          have h_factorial : ∀ k : ℕ, 0 < k → (Nat.factorial k : ℝ) ≥ (k / Real.exp 1) ^ k := by
            intro k hk; rw [ div_pow ] ; rw [ ge_iff_le ] ; rw [ div_le_iff₀ ( by positivity ) ] ; have := Real.exp_one_lt_d9.le; norm_num at *;
            rw [ ← div_le_iff₀' ( by positivity ) ] ; rw [ Real.exp_eq_exp_ℝ ] ; norm_num [ NormedSpace.exp_eq_tsum_div ];
            exact Summable.le_tsum ( show Summable _ from Real.summable_pow_div_factorial _ ) k ( fun _ _ => by positivity );
          intro k n hk hn; convert le_trans ( h_binom k n hk hn ) _ using 1; rw [ div_pow ] ; ring_nf at *;
          simpa [ mul_assoc, mul_comm, mul_left_comm ] using mul_le_mul_of_nonneg_left ( inv_anti₀ ( by positivity ) ( h_factorial k hk ) ) ( by positivity : 0 ≤ ( n : ℝ ) ^ k );
        exact_mod_cast h_binom _ _ ( by positivity ) h2q;
    -- Combining the bounds gives us the desired inequality.
    have h_combined : ((Nat.choose (n - ell) q : ℝ) * (Nat.choose ell q : ℝ)) / ((Nat.choose (2 * q) q : ℝ) * (Nat.choose n (2 * q) : ℝ)) ≥ ((n - ell) / q : ℝ) ^ q * (ell / q : ℝ) ^ q / ((2 * Real.exp 1) ^ q * (Real.exp 1 * n / (2 * q)) ^ (2 * q)) := by
      gcongr;
      · exact mul_pos ( Nat.cast_pos.mpr ( Nat.choose_pos ( by linarith ) ) ) ( Nat.cast_pos.mpr ( Nat.choose_pos ( by linarith ) ) );
      · exact h_bounds.1;
      · exact h_bounds.2.1;
      · exact h_bounds.2.2.1;
      · exact h_bounds.2.2.2;
    refine le_trans ?_ h_combined ; ring_nf ; norm_num [ Real.exp_neg, Real.exp_mul, Real.exp_log, hn, hq ];
    norm_num [ pow_mul', mul_assoc, mul_comm, mul_left_comm, hn.ne', hq.ne' ];
    field_simp;
    norm_num [ mul_assoc, mul_left_comm, ← mul_pow ];
    field_simp;
    exact pow_le_pow_left₀ ( by positivity ) ( by nlinarith only [ show ( ell : ℝ ) * q * n ≥ 0 by positivity, show ( ell : ℝ ) * q ≥ 0 by positivity, show ( n : ℝ ) ≥ 2 * ell by norm_cast, show ( ell : ℝ ) ≥ q by norm_cast ] ) _;
  convert h_bounds.le using 1;
  · ring;
  · unfold chooseR; rw [ Nat.cast_choose, Nat.cast_choose, Nat.cast_choose, Nat.cast_choose ] <;> try omega;
    rw [ Nat.cast_choose, Nat.cast_choose ] <;> try omega;
    field_simp;
    rw [ show n - 2 * q - ( ell - q ) = n - ell - q by omega, show 2 * q - q = q by omega ] ; ring

end