/-
Copyright (c) 2026 Prastik Mohanraj. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prastik Mohanraj
-/

import Mathlib.Algebra.Field.ZMod
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Data.Real.StarOrdered
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum.Basic
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.SplitIfs
import TCSlib.BooleanAnalysis.BLR.ZkFourier

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

open Finset Complex ZkFourier

namespace ZkBLR

set_option linter.unusedSectionVars false

/-!
# BLR Linearity Test on ℤ_k^n

## Main results

- `linear_iff_character`: a function f : ℤ_k^n → ℤ_k is linear iff it equals a dot-product character
- `re_toOmega_le_re_rootOfUnity`: Re(ω_k^a) ≤ cos(2π/k) for all nonzero a ∈ ℤ_k
- `re_fourier_coeff_upper_bound`: Re[f̂(s)] ≤ 1 − (1 − cos(2π/k)) · dist(f, χ_s)
- `BLR_completeness`: Pr[BLR accepts f] = 1 when f is linear
- `BLR_accept_prob_eq_fourier_sum`: Pr[accept] = (1/k) ∑_j ∑_s |f̂_j(s)|² · Re[f̂_j(s)]
- `BLR_soundness`: soundness for prime fields: Pr[accept] ≤ 1 − ((p−1)/p)(1 − cos(2π/p))ε
- `BLR_soundness_general`: soundness for arbitrary k: Pr[accept] ≤ 1 − (φ(k)/k)(1 − cos(2π/k))ε
- `BLR_soundness_prime`: general bound specializes to the prime-field bound for k = p prime

## References

- Original formalization by Prastik Mohanraj
-/

-- ============================================================================
-- SECTION 1: LINEAR_FUNCTIONS
-- ----------------------------------------------------------------------------
-- A function f : ℤ_k^n → ℤ_k is linear if f(x + y) = f(x) + f(y) for all
-- x, y ∈ ℤ_k^n. Equivalently, f is linear iff there exists a "coefficient
-- vector" s ∈ ℤ_k^n such that f(x) = s · x = ∑_i s_i x_i (the dot product
-- in ℤ_k). This identification means:
--   • every linear function is determined by its values on the n standard
--     basis vectors e_1, …, e_n;
--   • the "lifted" function x ↦ ω_k^{f(x)} is exactly the Fourier character
--     χ_s when f(x) = s · x.
--
-- We also define the Hamming distance dist(f,g) = Pr_x[f(x) ≠ g(x)] and the
-- notion of being ε-far from all linear functions, which is the starting
-- hypothesis for the BLR soundness theorem.
--
-- This is the ℤ_k generalization of the Boolean section in BoolBLR.lean,
-- where linearity was f(x ⊕ y) = f(x) ⊕ f(y) in F_2.
-- ============================================================================
section LINEAR_FUNCTIONS

variable {k : ℕ} [NeZero k] {n : ℕ}

-- f(x+y) = f(x) + f(y)
def is_linear (f : ZkVec k n → ZMod k) : Prop :=
  ∀ x y, f (x + y) = f x + f y

-- x ↦ ω_k^{f(x)}
noncomputable def lift_omega (f : ZkVec k n → ZMod k) : ZkFun k n :=
  fun x => toOmega (f x)

-- dist(f,g) = Pr[f(x) ≠ g(x)]
noncomputable def zk_dist (f g : ZkVec k n → ZMod k) : ℝ :=
  (∑ x : ZkVec k n, if f x = g x then (0 : ℝ) else 1) / (k : ℝ) ^ n

-- f is ε-far from linear iff dist(f,g) ≥ ε for all linear g
def epsilon_far_from_linear (f : ZkVec k n → ZMod k) (ε : ℝ) : Prop :=
  0 ≤ ε ∧ ε ≤ 1 ∧
  ∀ g : ZkVec k n → ZMod k, is_linear g → zk_dist f g ≥ ε

-- f linear ↔ ∃s, f(x) = s·x
lemma linear_iff_character (f : ZkVec k n → ZMod k) :
    is_linear f ↔ ∃ s : ZkVec k n, ∀ x, f x = zkDot s x := by
      refine' ⟨ fun h => _, _ ⟩;
      · use fun i => f ( Pi.single i 1 );
        intro x; induction' x using Pi.single_induction with i x ih; simp_all +decide [ zkDot ] ;
        · -- Base case: f(0) = 0 by linearity (f(0+0) = f(0)+f(0) implies f(0) = 0).
          simpa using h 0 0;
        · -- Additive step: f(x + y) = f(x) + f(y) by linearity.
          simp_all +decide [ is_linear, zkDot ];
          simp +decide only [mul_add, sum_add_distrib];
        · -- Scalar step: f(m · e_i) = m · f(e_i) by induction on m.
          rename_i i m;
          have h_ind : ∀ m : ℕ, f (Pi.single i (m : ZMod k)) = m * f (Pi.single i 1) := by
            intro m; induction m <;> simp_all +decide [ add_mul, Pi.single_add ] ;
            · simpa using h 0 0;
            · rw [ h, ‹f ( Pi.single i _ ) = _› ];
          convert h_ind ( m.val ) using 1 <;> simp +decide [ zkDot ];
          rw [ Finset.sum_eq_single i ] <;> simp +contextual [ mul_comm ];
      · -- (⇐) direction: if f(x) = s · x, linearity follows from dot product bilinearity.
        rintro ⟨ s, hs ⟩ ; intro x y; simp +decide [ hs, zkDot_add_right ] ;

-- The canonical linear function with coefficient vector s:
--   linear_character s = (x ↦ s · x).
noncomputable def linear_character (s : ZkVec k n) :
    ZkVec k n → ZMod k :=
  fun x => zkDot s x

end LINEAR_FUNCTIONS

-- ============================================================================
-- SECTION 2: NORMALIZATION
-- ----------------------------------------------------------------------------
-- A function f : ℤ_k^n → ℤ_k is *normalized* if f(0) = 0. Every linear
-- function is automatically normalized (since f(0+0) = f(0)+f(0) implies
-- f(0) = 0). We can normalize any function by subtracting f(0):
--   (normalize f)(x) = f(x) - f(0).
--
-- Normalization is a technical convenience: it does not change the distance
-- to linear functions, but it simplifies certain Fourier-analytic arguments
-- because the "constant term" f(0) is pinned to zero. The BLR soundness
-- theorem is stated for normalized functions that are ε-far from linear.
-- ============================================================================
section NORMALIZATION

variable {k : ℕ} [NeZero k] {n : ℕ}

-- A function is normalized if its value at the origin is zero.
-- This is automatic for linear functions and harmless for the BLR analysis.
def normalized
    (f : ZkVec k n → ZMod k) : Prop :=
  f 0 = 0

-- The normalization operator: subtract the constant f(0) to ensure
-- the resulting function vanishes at the origin.
def normalize
    (f : ZkVec k n → ZMod k) :
    ZkVec k n → ZMod k :=
  fun x => f x - f 0

-- normalize f evaluates to 0 at the origin: (normalize f)(0) = f(0) - f(0) = 0.
lemma normalize_zero
    (f : ZkVec k n → ZMod k) :
    normalize f 0 = 0 := by
  unfold normalize
  simp

-- Every linear function is normalized: f(0) = 0.
-- Proof: f(0) = f(0 + 0) = f(0) + f(0), so f(0) = 0.
lemma linear_normalized
    (f : ZkVec k n → ZMod k)
    (hlin : is_linear f) :
    normalized f := by
  unfold normalized
  simpa using hlin 0 0

-- Combined condition for the soundness theorem: f is normalized AND ε-far
-- from every linear function. This bundles the normalization hypothesis
-- with the distance requirement for cleaner theorem statements.
def epsilon_far_from_linear_normalized
    (f : ZkVec k n → ZMod k)
    (ε : ℝ) : Prop :=
  normalized f ∧
  0 ≤ ε ∧ ε ≤ 1 ∧
  ∀ g : ZkVec k n → ZMod k,
    is_linear g →
    zk_dist f g ≥ ε

end NORMALIZATION

-- ============================================================================
-- SECTION 3: FOURIER_BOUNDS
-- ----------------------------------------------------------------------------
-- This section establishes the key Fourier-analytic bound that connects
-- the real part of a Fourier coefficient to the distance from linearity:
--
--   Re[f̂(s)] ≤ 1 − (1 − cos(2π/k)) · dist(f, linear_character s).
--
-- The constant 1 − cos(2π/k) arises because ω_k^a lies on the unit circle,
-- and for any nonzero a ∈ ℤ_k, the real part of ω_k^a is at most cos(2π/k).
-- This is the "penalty" for each disagreement between f and the linear
-- function x ↦ s · x: on inputs where f(x) ≠ s · x, the product
-- ω_k^{f(x)} · conj(ω_k^{s·x}) has real part ≤ cos(2π/k) instead of 1.
--
-- When k = 2 (the Boolean case), cos(2π/2) = cos(π) = −1, so the constant
-- becomes 1 − (−1) = 2, recovering the bound f̂(S) ≤ 1 − 2·dist(f, χ_S)
-- from BoolBLR.lean.
--
-- As a corollary, if f is ε-far from every linear function, then
--   Re[f̂(s)] ≤ 1 − (1 − cos(2π/k)) · ε   for all s.
-- ============================================================================
section FOURIER_BOUNDS

variable {k : ℕ} [NeZero k] {n : ℕ}

-- Re[(ω_k^a)] ≤ cos(2π/k) for all nonzero a ∈ Z_k
lemma re_toOmega_le_re_rootOfUnity {k : ℕ} [NeZero k] (hk : 2 ≤ k) (a : ZMod k) (ha : a ≠ 0) :
    (toOmega a).re ≤ Real.cos (2 * Real.pi / k) := by
  -- Since a ≠ 0 in ℤ_k, we have 1 ≤ a.val ≤ k − 1.
  have h_a_val : 1 ≤ a.val ∧ a.val ≤ k - 1 := by
    exact ⟨ Nat.pos_of_ne_zero ( by simpa [ ZMod.val_eq_zero ] using ha ), Nat.le_pred_of_lt ( ZMod.val_lt a ) ⟩;
  -- The angle θ = 2πa/k satisfies 2π/k ≤ θ ≤ 2π − 2π/k.
  have h_angle : 2 * Real.pi / k ≤ 2 * Real.pi * a.val / k ∧ 2 * Real.pi * a.val / k ≤ 2 * Real.pi - 2 * Real.pi / k := by
    field_simp;
    exact ⟨ mod_cast h_a_val.1, le_tsub_of_add_le_right <| mod_cast h_a_val.2.trans_lt <| Nat.pred_lt <| ne_bot_of_gt hk ⟩;
  -- cos(θ) ≤ cos(2π/k) because cos is decreasing on [0, π] and
  -- increasing on [π, 2π] (using the identity cos(2π − θ) = cos(θ)).
  have h_cos_decreasing : Real.cos (2 * Real.pi * a.val / k) ≤ Real.cos (2 * Real.pi / k) := by
    by_cases h_case : 2 * Real.pi * a.val / k ≤ Real.pi;
    · exact Real.cos_le_cos_of_nonneg_of_le_pi ( by positivity ) ( by linarith ) h_angle.1;
    · rw [ ← Real.cos_two_pi_sub ] ; exact Real.cos_le_cos_of_nonneg_of_le_pi ( by nlinarith [ Real.pi_pos, show ( k : ℝ ) ≥ 2 by norm_cast, mul_div_cancel₀ ( 2 * Real.pi ) ( by positivity : ( k : ℝ ) ≠ 0 ) ] ) ( by nlinarith [ Real.pi_pos, show ( k : ℝ ) ≥ 2 by norm_cast, mul_div_cancel₀ ( 2 * Real.pi ) ( by positivity : ( k : ℝ ) ≠ 0 ) ] ) ( by nlinarith [ Real.pi_pos, show ( k : ℝ ) ≥ 2 by norm_cast, mul_div_cancel₀ ( 2 * Real.pi ) ( by positivity : ( k : ℝ ) ≠ 0 ) ] ) ;
  -- Finally, Re(ω_k^a) = cos(2πa/k) ≤ cos(2π/k).
  convert h_cos_decreasing using 1 ; unfold toOmega ; norm_num [ Complex.exp_re, Complex.exp_im, Complex.cos ] ; ring_nf;
  unfold rootOfUnity; norm_num [ ← Complex.exp_nat_mul, Complex.exp_re ] ; ring_nf;
  norm_num [ ZMod.cast, ZMod.val ];
  rcases k with ( _ | _ | k ) <;> norm_num at *

/-
`Re[f̂(s)] ≤ 1 − (1 − cos(2π/k)) · dist(f, χ_s)` for general `k ≥ 2`.
-/
lemma re_fourier_coeff_upper_bound
    (hk : 2 ≤ k)
    (f : ZkVec k n → ZMod k)
    (s : ZkVec k n) :
    (fourier_coeff (lift_omega f) s).re
      ≤ 1 - (1 - Real.cos (2 * Real.pi / k)) *
        zk_dist f (linear_character s) := by
  unfold fourier_coeff zk_dist; norm_num [ Finset.sum_ite ] ; ring_nf;
  norm_num [ inner_product, lift_omega, char_s ];
  -- Pointwise bound: on each x, the real part of ω_k^{f(x)} · conj(ω_k^{s·x})
  -- is ≤ 1 − (1 − cos(2π/k)) · 𝟙[f(x) ≠ s·x].
  have h_bound : ∀ x : ZkVec k n, (toOmega (f x) * (starRingEnd ℂ) (toOmega (zkDot s x))).re ≤ 1 - (1 - Real.cos (2 * Real.pi / k)) * (if f x = linear_character s x then 0 else 1) := by
    intro x
    by_cases hfx : f x = linear_character s x;
    · -- Agreement case: the product is |ω_k^{s·x}|² = 1.
      simp_all +decide [ linear_character ];
      unfold toOmega ; ring_nf;
      norm_num [ ← Complex.normSq_add_mul_I, Complex.normSq_eq_norm_sq, Complex.norm_exp ];
      unfold rootOfUnity; norm_num [ Complex.norm_exp ] ;
    · -- Disagreement case: ω_k^{f(x) − s·x} has Re ≤ cos(2π/k).
      have h_ineq : (toOmega (f x - zkDot s x)).re ≤ Real.cos (2 * Real.pi / k) := by
        apply re_toOmega_le_re_rootOfUnity hk;
        exact sub_ne_zero_of_ne hfx;
      -- Rewrite ω_k^{f(x) − s·x} = ω_k^{f(x)} · conj(ω_k^{s·x}).
      have h_ineq : toOmega (f x - zkDot s x) = toOmega (f x) * (starRingEnd ℂ) (toOmega (zkDot s x)) := by
        have h_ineq : toOmega (f x - zkDot s x) = toOmega (f x) * toOmega (-zkDot s x) := by
          convert toOmega_add ( f x ) ( -zkDot s x ) using 1 ; ring_nf;
        rw [ h_ineq, ← toOmega_neg ];
      aesop;
  -- Average the pointwise bound over all x ∈ ℤ_k^n.
  convert div_le_div_of_nonneg_right ( Finset.sum_le_sum fun x _ => h_bound x ) ( by positivity : ( 0 : ℝ ) ≤ k ^ n ) using 1 <;> norm_num [ Finset.sum_ite ] ; ring_nf;
  any_goals exact Finset.univ;
  · unfold expectation; norm_num [ Complex.ext_iff ] ; ring_nf;
    norm_num [ Complex.ext_iff, Finset.sum_mul _ _ _ ];
    norm_cast ; norm_num [ mul_pow ];
  · rw [ show ( #univ : ℕ ) = k ^ n from ?_ ] ; ring_nf;
    · norm_num [ add_comm, NeZero.ne ];
    · simp +decide [ Finset.card_univ, ZkVec ]

/-
If `f` is ε-far from linear, then `Re[f̂(s)] ≤ 1 − (1 − cos(2π/k))ε`.
-/
lemma re_epsilon_far_bounds_fourier
    (hk : 2 ≤ k)
    (f : ZkVec k n → ZMod k)
    (ε : ℝ)
    (hfar : epsilon_far_from_linear_normalized f ε)
    (s : ZkVec k n) :
    (fourier_coeff (lift_omega f) s).re
      ≤ 1 - (1 - Real.cos (2 * Real.pi / k)) * ε := by
  -- Apply the pointwise bound, then use ε ≤ dist(f, linear_character s).
  refine' le_trans ( re_fourier_coeff_upper_bound hk f s ) _;
  gcongr;
  -- The constant 1 − cos(2π/k) is nonneg (since cos(2π/k) ≤ 1).
  · nlinarith [ Real.cos_sq' ( 2 * Real.pi / k ) ];
  -- dist(f, linear_character s) ≥ ε because linear_character s is linear.
  · exact hfar.2.2.2 _ ( show is_linear ( linear_character s ) from fun x y => by simp +decide [ linear_character, zkDot_add_right ] )

end FOURIER_BOUNDS

-- ============================================================================
-- SECTION 4: BLR_TEST_SETUP
-- ----------------------------------------------------------------------------
-- This section defines the BLR linearity test and its acceptance probability
-- for functions f : ℤ_k^n → ℤ_k:
--
--   1. Pick x, y ∈ ℤ_k^n uniformly and independently at random.
--   2. Query f(x), f(y), and f(x + y).
--   3. Accept iff f(x + y) = f(x) + f(y).
--
-- We also define the "j-twisted lift" x ↦ ω_k^{j·f(x)} for j ∈ ℤ_k,
-- which parametrizes a family of Fourier analyses indexed by j. The case
-- j = 1 recovers the standard lift ω_k^{f(x)}, while j = 0 gives the
-- constant function 1. Summing over all j ∈ ℤ_k allows us to express the
-- acceptance indicator 𝟙[f(x+y) = f(x) + f(y)] in terms of roots of
-- unity, which is the key step in the Fourier-analytic soundness proof.
-- ============================================================================
section BLR_TEST_SETUP

variable {k : ℕ} [NeZero k] {n : ℕ}

-- x ↦ ω_k^{j f(x)}
noncomputable def lift_omega_j (j : ZMod k) (f : ZkVec k n → ZMod k) :
    ZkFun k n :=
  fun x => toOmega (j * f x)

-- Pr[BLR accepts f]
noncomputable def BLR_accept_prob (f : ZkVec k n → ZMod k) : ℝ :=
  (∑ x : ZkVec k n, ∑ y : ZkVec k n,
    if f (x + y) = f x + f y then (1 : ℝ) else 0) / ((k : ℝ) ^ n) ^ 2

-- Pr[BLR accepts f] = 1 if f is linear
lemma BLR_completeness (f : ZkVec k n → ZMod k) (hlin : is_linear f) :
    BLR_accept_prob f = 1 := by
      unfold BLR_accept_prob;
      rw [ div_eq_iff ] <;> norm_cast <;> norm_num [ hlin ];
      -- Every (x, y) pair satisfies the test, so the sum equals k^{2n}.
      · simp_all +decide [ is_linear ];
        rw [ sq, card_ZkVec ];
      · exact fun h => absurd h ( NeZero.ne k )

end BLR_TEST_SETUP

-- ============================================================================
-- SECTION 5: BLR_FOURIER
-- ----------------------------------------------------------------------------
-- This section develops the Fourier-analytic expression for the BLR
-- acceptance probability. The key identity is:
--
--   Pr[BLR accepts f] = (1/k) ∑_{j ∈ ℤ_k} ∑_{s ∈ ℤ_k^n}
--                          |f̂_j(s)|² · Re[f̂_j(s)]
--
-- where f̂_j(s) is the Fourier coefficient of the j-twisted lift
-- x ↦ ω_k^{j·f(x)}. The derivation proceeds in several steps:
--
-- 1. Express the acceptance indicator 𝟙[a = 0] as (1/k) ∑_j ω_k^{ja}
--    (applied with a = f(x+y) − f(x) − f(y)).
-- 2. For each fixed j, recognize ∑_{x,y} ω_k^{j(f(x+y)−f(x)−f(y))} as a
--    triple product expectation E[F(x+y) · F̄(x) · F̄(y)] with F = lift_omega_j j f.
-- 3. Expand this triple product using Fourier analysis to get
--    ∑_s |F̂(s)|² · conj(F̂(s)).
-- 4. Take the real part and sum over j.
--
-- We also establish the j=0 contribution (which is always 1) and a trivial
-- Parseval-based upper bound of 1 for each j's contribution.
-- ============================================================================
section BLR_FOURIER

variable {k : ℕ} [NeZero k] {n : ℕ}

/-- `∑_j ω_k^{ja} = k` if `a = 0`, and `0` otherwise. -/
lemma geom_sum_toOmega_dual (a : ZMod k) :
    ∑ j : ZMod k, toOmega (j * a) = if a = 0 then (k : ℂ) else 0 := by
  simp_rw [mul_comm]; exact geom_sum_toOmega a

/-- `1[a=0] = (1/k) · Re[∑_j ω_k^{ja}]`. -/
lemma indicator_eq_char_sum_re (a : ZMod k) :
    (if a = 0 then (1 : ℝ) else 0) =
    (1 / (k : ℝ)) * (∑ j : ZMod k, toOmega (j * a)).re := by
  have h := geom_sum_toOmega_dual a
  split_ifs at * <;> simp_all +decide [NeZero.ne]

/-
Parseval identity for `x ↦ ω_k^{j·f(x)}`: `∑_s |f̂_j(s)|² = 1`.
-/
lemma parseval_lift_omega_j
    (j : ZMod k) (f : ZkVec k n → ZMod k) :
    ∑ s : ZkVec k n,
      ‖fourier_coeff (lift_omega_j j f) s‖ ^ 2 = 1 := by
  convert parseval_identity ( fun x => toOmega ( j * f x ) ) using 1;
  unfold L2_norm_sq;
  -- Each |ω_k^{j·f(x)}|² = 1, so the sum is k^n / k^n = 1.
  simp +decide [ norm_toOmega ];
  rw [ card_ZkVec, eq_div_iff ] <;> norm_cast <;> aesop

/-
E[E[F(x+y) conj(F(x)) conj(F(y))]] = ∑_s |F̂(s)|² conj(F̂(s)).
-/
lemma triple_product_fourier (j : ZMod k) (f : ZkVec k n → ZMod k) :
    expectation (fun x => expectation (fun y =>
      lift_omega_j j f (x + y) * starRingEnd ℂ (lift_omega_j j f x) *
        starRingEnd ℂ (lift_omega_j j f y)))
    = ∑ s : ZkVec k n,
        ‖fourier_coeff (lift_omega_j j f) s‖ ^ 2 *
        starRingEnd ℂ (fourier_coeff (lift_omega_j j f) s) := by
  -- We prove the identity for an arbitrary function F : ℤ_k^n → ℂ,
  -- then specialize to F = lift_omega_j j f.
  have h_fourier : ∀ (F : ZkFun k n), expectation (fun x => expectation (fun y => F (x + y) * starRingEnd ℂ (F x) * starRingEnd ℂ (F y))) = ∑ s : ZkVec k n, ‖fourier_coeff F s‖ ^ 2 * starRingEnd ℂ (fourier_coeff F s) := by
    intro F;
    -- Step 1: Expand F(x+y) = ∑_s F̂(s) χ_s(x+y) using the Fourier expansion.
    have h_fourier_expansion : ∀ x y : ZkVec k n, F (x + y) = ∑ s : ZkVec k n, fourier_coeff F s * char_s s (x + y) := by
      exact fun x y => fourier_expansion F ( x + y );
    -- Step 2: Substitute and exchange the order of summation (Fubini).
    -- After expanding, the triple sum over (x, y, s) is rearranged to
    -- ∑_s F̂(s) · (∑_x F̄(x) χ_s(x)) · (∑_y F̄(y) χ_s(y)).
    have h_exchange_sum : ∑ x : ZkVec k n, ∑ y : ZkVec k n, F (x + y) * starRingEnd ℂ (F x) * starRingEnd ℂ (F y) = ∑ s : ZkVec k n, fourier_coeff F s * ∑ x : ZkVec k n, starRingEnd ℂ (F x) * char_s s x * ∑ y : ZkVec k n, starRingEnd ℂ (F y) * char_s s y := by
      simp +decide only [h_fourier_expansion, char_s_add, mul_left_comm, sum_mul, mul_assoc, Finset.mul_sum _ _ _];
      exact Eq.symm ( Finset.sum_comm.trans ( Finset.sum_congr rfl fun _ _ => Finset.sum_comm.trans ( Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring ) ) );
    -- Step 3: Recognize ∑_x F̄(x) χ_s(x) = conj(F̂(s)) · k^n.
    -- This uses the definition F̂(s) = E[F · χ̄_s] = (1/k^n) ∑ F(x) conj(χ_s(x)),
    -- so ∑ F̄(x) χ_s(x) = conj(∑ F(x) χ̄_s(x)) = conj(F̂(s) · k^n) = conj(F̂(s)) · k^n.
    have h_inner_sum : ∀ s : ZkVec k n, ∑ x : ZkVec k n, starRingEnd ℂ (F x) * char_s s x = starRingEnd ℂ (fourier_coeff F s) * (k : ℂ) ^ n := by
      intro s
      have h_inner_sum : ∑ x : ZkVec k n, starRingEnd ℂ (F x) * char_s s x = starRingEnd ℂ (∑ x : ZkVec k n, F x * starRingEnd ℂ (char_s s x)) := by
        simp +decide [ mul_comm];
      simp_all +decide [ fourier_coeff ];
      unfold inner_product; simp +decide [ mul_comm ] ;
      unfold expectation; simp +decide [ mul_comm ] ;
      rw [ mul_div_cancel₀ _ ( by norm_cast; exact pow_ne_zero _ ( NeZero.ne k ) ) ];
    -- Step 4: Combine: ∑_s F̂(s) · |conj(F̂(s)) · k^n|² / k^{2n}
    -- simplifies to ∑_s |F̂(s)|² · conj(F̂(s)).
    simp_all +decide [ ← mul_assoc, ← Finset.sum_mul, expectation ];
    simp_all +decide [ ← Finset.sum_div _ _ _, div_eq_iff, NeZero.ne ];
    simp +decide [ mul_assoc, mul_comm, Finset.mul_sum _ _ _, Complex.mul_conj, Complex.normSq_eq_norm_sq ];
  exact h_fourier _

/-
BLR acceptance probability equals `(1/k) ∑_j ∑_s |f̂_j(s)|² Re[f̂_j(s)]`.
-/
lemma BLR_accept_prob_eq_fourier_sum
    (f : ZkVec k n → ZMod k) :
    BLR_accept_prob f =
    (1 / (k : ℝ)) *
      ∑ j : ZMod k,
        ∑ s : ZkVec k n,
          ‖fourier_coeff (lift_omega_j j f) s‖ ^ 2 *
            (fourier_coeff (lift_omega_j j f) s).re := by
  -- Step 1: Replace the acceptance indicator with a character sum.
  have h_indicator : ∀ x y : ZkVec k n, (if f (x + y) = f x + f y then (1 : ℝ) else 0) = (1 / (k : ℝ)) * (∑ j : ZMod k, (toOmega (j * (f (x + y) - f x - f y))).re) := by
    intro x y; have := indicator_eq_char_sum_re ( f ( x + y ) - f x - f y ) ; simp_all +decide [ sub_eq_iff_eq_add' ] ;
  -- Step 2: Apply the triple product identity to rewrite each j-sum
  -- as k^{2n} · (∑_s |f̂_j(s)|² · Re[f̂_j(s)]).
  have h_triple_product : ∀ j : ZMod k, ∑ x : ZkVec k n, ∑ y : ZkVec k n, (toOmega (j * (f (x + y) - f x - f y))).re = (k : ℝ) ^ (2 * n) * (∑ s : ZkVec k n, ‖fourier_coeff (lift_omega_j j f) s‖ ^ 2 * (fourier_coeff (lift_omega_j j f) s).re) := by
    intro j
    -- Work in ℂ first, then take real parts.
    have h_triple_product : ∑ x : ZkVec k n, ∑ y : ZkVec k n, (toOmega (j * (f (x + y) - f x - f y))) = (k : ℂ) ^ (2 * n) * (∑ s : ZkVec k n, ‖fourier_coeff (lift_omega_j j f) s‖ ^ 2 * starRingEnd ℂ (fourier_coeff (lift_omega_j j f) s)) := by
      convert congr_arg ( fun x : ℂ => ( k : ℂ ) ^ ( 2 * n ) * x ) ( triple_product_fourier j f ) using 1;
      -- Rewrite ω_k^{j(f(x+y)−f(x)−f(y))} = ω_k^{jf(x+y)} · conj(ω_k^{jf(x)}) · conj(ω_k^{jf(y)})
      -- using toOmega_add and toOmega_neg.
      unfold expectation lift_omega_j; ring_nf;
      simp +decide [ pow_mul', mul_assoc, mul_comm, mul_left_comm, Finset.mul_sum _ _ _ ];
      refine' Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun y _ => _ ; ring_nf;
      simp +decide [ mul_comm, mul_left_comm, sub_eq_add_neg ];
      simp +decide [ toOmega_add, toOmega_neg ];
    -- Take real parts on both sides.
    convert congr_arg Complex.re h_triple_product using 1;
    · simp +decide ;
    · norm_num [ Complex.ext_iff, pow_mul' ];
      norm_cast ; norm_num;
  -- Step 3: Combine the indicator substitution with the triple product identity,
  -- rearrange sums, and simplify the normalizing factors.
  unfold BLR_accept_prob;
  simp +decide only [h_indicator];
  simp +decide [ ← Finset.mul_sum _ _ _ ];
  rw [ Finset.sum_comm ];
  rw [ Finset.sum_comm, Finset.sum_congr rfl fun _ _ => Finset.sum_comm ];
  rw [ Finset.sum_comm, Finset.sum_congr rfl fun _ _ => h_triple_product _ ] ; ring_nf;
  simp +decide [ Finset.mul_sum _ _ _, mul_assoc, mul_left_comm, NeZero.ne ]

/-
The `j = 0` contribution to the BLR Fourier sum equals `1`.
-/
lemma lift_omega_j_zero_contribution
    (f : ZkVec k n → ZMod k) :
    ∑ s : ZkVec k n,
      ‖fourier_coeff (lift_omega_j 0 f) s‖ ^ 2 *
        (fourier_coeff (lift_omega_j 0 f) s).re = 1 := by
  unfold fourier_coeff;
  unfold inner_product;
  -- When j = 0, lift_omega_j 0 f ≡ 1, so ⟨1, χ_s⟩ = 0 for s ≠ 0.
  have h_nonzero : ∀ s : ZkVec k n, s ≠ 0 → expectation (fun x => lift_omega_j 0 f x * starRingEnd ℂ (char_s s x)) = 0 := by
    intros s hs_nonzero
    -- The expectation reduces to E[conj(χ_s)] = E[χ_{-s}] = 0 since s ≠ 0.
    have h_exp : expectation (fun x => starRingEnd ℂ (char_s s x)) = 0 := by
      have h_exp : expectation (fun x => char_s (-s) x) = 0 := by
        exact expectation_char_nontrivial ( neg_ne_zero.mpr hs_nonzero );
      simp_rw [ZkFourier.char_s_conj]; exact h_exp;
    unfold lift_omega_j at *; simp_all +decide [ expectation ] ;
  -- Only the s = 0 term survives; it contributes |1|² · Re(1) = 1.
  rw [ Finset.sum_eq_single 0 ] <;> simp_all +decide;
  unfold expectation; norm_num [ Finset.sum_const, nsmul_eq_mul, NeZero.ne ] ;
  unfold lift_omega_j; norm_num [ toOmega_zero ] ;
  rw [ show Fintype.card ( ZkVec k n ) = k ^ n from ?_ ] ; norm_num [ NeZero.ne ];
  convert card_ZkVec k n

/-
Weighted Fourier sum bounded by 1 for any `j` (trivial Parseval bound).
-/
lemma weighted_fourier_sum_le_one
    (j : ZMod k) (f : ZkVec k n → ZMod k) :
    ∑ s : ZkVec k n,
      ‖fourier_coeff (lift_omega_j j f) s‖ ^ 2 *
        (fourier_coeff (lift_omega_j j f) s).re
      ≤ 1 := by
  -- First bound Re[f̂_j(s)] ≤ ‖f̂_j(s)‖ (Re of a complex number ≤ its norm).
  refine' le_trans ( Finset.sum_le_sum fun s _ => mul_le_mul_of_nonneg_left ( Complex.re_le_norm _ ) ( sq_nonneg _ ) ) _;
  -- Then bound ‖f̂_j(s)‖ ≤ 1 using Parseval: ‖f̂_j(s)‖² ≤ ∑_t ‖f̂_j(t)‖² = 1.
  refine' le_trans ( Finset.sum_le_sum fun i _ => mul_le_of_le_one_right ( sq_nonneg _ ) _ ) _;
  · have := parseval_lift_omega_j j f;
    exact le_trans ( Real.le_sqrt_of_sq_le ( Finset.single_le_sum ( fun s _ => sq_nonneg ( ‖fourier_coeff ( lift_omega_j j f ) s‖ ) ) ( Finset.mem_univ i ) ) ) ( by norm_num [ this ] );
  -- Finally, ∑_s ‖f̂_j(s)‖² · ‖f̂_j(s)‖ ≤ ∑_s ‖f̂_j(s)‖² = 1.
  · convert parseval_lift_omega_j j f |> le_of_eq

end BLR_FOURIER

-- ============================================================================
-- SECTION 6: PRIME_FIELD_SOUNDNESS
-- ----------------------------------------------------------------------------
-- When k = p is prime, ℤ_p is a field and every nonzero element is a unit.
-- This simplifies the Fourier analysis: the Parseval identity ∑|f̂(s)|² = 1
-- combined with the per-coefficient bound Re[f̂(s)] ≤ 1 − (1−cos(2π/p))ε
-- gives ∑_s |f̂(s)|² · Re[f̂(s)] ≤ 1 − (1−cos(2π/p))ε.
--
-- The cube sum bound ∑|f̂(s)|³ ≤ A · ∑|f̂(s)|² is a general inequality
-- used in some alternative formulations of BLR soundness.
-- ============================================================================
section PRIME_FIELD_SOUNDNESS

variable {p : ℕ} [Fact p.Prime] {n : ℕ}

-- Throughout this section, p is prime, so ZMod p is a field.

-- ∑_s |f̂(s)|³ ≤ A · ∑_s |f̂(s)|² whenever |f̂(s)| ≤ A for all s
lemma cube_sum_bound_by_max
    (f : ZkVec p n → ZMod p)
    (A : ℝ)
    (hA :
      ∀ s : ZkVec p n,
        ‖fourier_coeff (lift_omega f) s‖ ≤ A) :
    ∑ s : ZkVec p n,
      ‖fourier_coeff (lift_omega f) s‖ ^ 3
      ≤
      A *
      ∑ s : ZkVec p n,
        ‖fourier_coeff (lift_omega f) s‖ ^ 2 := by
  classical
  -- Pointwise bound: |f̂(s)|³ = |f̂(s)| · |f̂(s)|² ≤ A · |f̂(s)|².
  have hpoint :
      ∀ s : ZkVec p n,
        ‖fourier_coeff (lift_omega f) s‖ ^ 3
        ≤
        A * ‖fourier_coeff (lift_omega f) s‖ ^ 2 := by
    intro s
    have hs_nonneg :
        0 ≤ ‖fourier_coeff (lift_omega f) s‖ := norm_nonneg _
    have hsq_nonneg :
        0 ≤ ‖fourier_coeff (lift_omega f) s‖ ^ 2 := by
      positivity
    have hs_le : ‖fourier_coeff (lift_omega f) s‖ ≤ A := hA s
    calc
      ‖fourier_coeff (lift_omega f) s‖ ^ 3
          = ‖fourier_coeff (lift_omega f) s‖ *
            ‖fourier_coeff (lift_omega f) s‖ ^ 2 := by
              ring
      _ ≤ A * ‖fourier_coeff (lift_omega f) s‖ ^ 2 := by
            gcongr
  -- Sum the pointwise bounds and factor out A.
  calc
    ∑ s : ZkVec p n,
        ‖fourier_coeff (lift_omega f) s‖ ^ 3
      ≤
      ∑ s : ZkVec p n,
        A * ‖fourier_coeff (lift_omega f) s‖ ^ 2 := by
          exact Finset.sum_le_sum (fun s _ => hpoint s)
    _ =
      A *
      ∑ s : ZkVec p n,
        ‖fourier_coeff (lift_omega f) s‖ ^ 2 := by
          rw [Finset.mul_sum]

-- Parseval identity for the lifted function x ↦ ω_p^{f(x)}
lemma parseval_lift_omega
    (f : ZkVec p n → ZMod p) :
    ∑ s : ZkVec p n,
      ‖fourier_coeff (lift_omega f) s‖ ^ 2 = 1 := by
  rw [parseval_identity]
  unfold L2_norm_sq
  -- Each |ω_p^{f(x)}|² = 1, so the sum is k^n / k^n = 1.
  have hnorm :
      ∀ x : ZkVec p n,
        ‖lift_omega f x‖ ^ 2 = (1 : ℝ) := by
    intro x
    unfold lift_omega
    rw [norm_toOmega]
    norm_num
  simp [hnorm, card_ZkVec]

-- ∑_s |f̂(s)|² Re[f̂(s)] ≤ 1 - (1 - cos(2π/p)) ε
lemma weighted_fourier_sum_bound
    (f : ZkVec p n → ZMod p)
    (ε : ℝ)
    (hfar : epsilon_far_from_linear_normalized f ε) :
    ∑ s : ZkVec p n,
      ‖fourier_coeff (lift_omega f) s‖ ^ 2 *
        (fourier_coeff (lift_omega f) s).re
      ≤
      1 -
      (1 - Real.cos (2 * Real.pi / p)) * ε := by
  -- Bound each term: |f̂(s)|² · Re[f̂(s)] ≤ |f̂(s)|² · (1 − (1−cos(2π/p))ε).
  refine' le_trans ( Finset.sum_le_sum fun s _ => mul_le_mul_of_nonneg_left ( re_epsilon_far_bounds_fourier (Nat.Prime.two_le Fact.out) f ε hfar s ) ( sq_nonneg _ ) ) _;
  -- Sum: ∑|f̂(s)|² · (1 − cε) = (∑|f̂(s)|²) · (1 − cε) = 1 · (1 − cε).
  rw [ ← Finset.sum_mul _ _ _, parseval_lift_omega f, one_mul ]

end PRIME_FIELD_SOUNDNESS

-- ============================================================================
-- SECTION 7: BLR_TEST_SOUNDNESS_PRIME
-- ----------------------------------------------------------------------------
-- BLR soundness for prime fields: if f : ℤ_p^n → ℤ_p is ε-far from every
-- linear function, then
--   Pr[BLR accepts f] ≤ 1 − ((p−1)/p) · (1 − cos(2π/p)) · ε.
--
-- The proof uses the Fourier decomposition of the acceptance probability
-- from Section 5:
--   Pr[accept] = (1/p) ∑_{j=0}^{p-1} ∑_s |f̂_j(s)|² · Re[f̂_j(s)].
--
-- The j = 0 term contributes 1 (by lift_omega_j_zero_contribution).
-- For each j ≠ 0 (and in the prime case, every j ≠ 0 is a unit), the
-- multiplication-by-j trick shows that the function g(x) = j·f(x) is
-- also ε-far from linear, so the weighted Fourier sum for j is bounded by
-- 1 − (1 − cos(2π/p))ε. Averaging over all p values of j gives the result.
-- ============================================================================
section BLR_TEST_SOUNDNESS_PRIME

variable {p : ℕ} [Fact p.Prime] {n : ℕ}

-- If f is ε-far from linear, then
-- Re[(lift_omega_j f)^̂(s)] ≤ 1 - (1 - cos(2π/k)) ε for all j ≠ 0
lemma re_fourier_coeff_lift_omega_j_bound
    (f : ZkVec p n → ZMod p)
    (ε : ℝ)
    (hfar : epsilon_far_from_linear_normalized f ε)
    (j : ZMod p) (hj : j ≠ 0)
    (s : ZkVec p n) :
    (fourier_coeff (lift_omega_j j f) s).re
      ≤ 1 - (1 - Real.cos (2 * Real.pi / p)) * ε := by
  -- Define g(x) = j · f(x).
  set g : ZkVec p n → ZMod p := fun x => j * f x;
  -- g is ε-far from linear: multiplication by the unit j permutes
  -- linear functions, so dist(g, linear) = dist(f, linear) ≥ ε.
  have hg_far : epsilon_far_from_linear_normalized g ε := by
    refine' ⟨ _, hfar.2.1, hfar.2.2.1, fun g' hg' => _ ⟩;
    · exact mul_eq_zero_of_right _ ( hfar.1 );
    · convert hfar.2.2.2 ( fun x => j⁻¹ * g' x ) ( by
        intro x y; simp +decide [ hg' x y, mul_add ] ; ) using 1;
      unfold zk_dist;
      grind +splitImp;
  -- Since f̂_j(s) = ĝ(s), the bound follows from re_epsilon_far_bounds_fourier.
  convert re_epsilon_far_bounds_fourier (Nat.Prime.two_le Fact.out) g ε hg_far s using 1

-- ∑_s |f̂_j(s)|² Re[f̂_j(s)]
-- ≤ 1 - (1 - cos(2π/k)) ε for every nonzero j
lemma weighted_sum_lift_omega_j_bound
    (f : ZkVec p n → ZMod p)
    (ε : ℝ)
    (hfar : epsilon_far_from_linear_normalized f ε)
    (j : ZMod p) (hj : j ≠ 0) :
    ∑ s : ZkVec p n,
      ‖fourier_coeff (lift_omega_j j f) s‖ ^ 2 *
        (fourier_coeff (lift_omega_j j f) s).re
      ≤ 1 - (1 - Real.cos (2 * Real.pi / p)) * ε := by
  refine le_trans (Finset.sum_le_sum fun s _ =>
    mul_le_mul_of_nonneg_left
      (re_fourier_coeff_lift_omega_j_bound f ε hfar j hj s)
      (sq_nonneg _)) ?_
  rw [← Finset.sum_mul, parseval_lift_omega_j j f, one_mul]

-- If f is ε-far from linear, then
-- Pr[BLR accepts f]
-- ≤ 1 - ((k-1)/k)(1 - cos(2π/k)) ε
lemma BLR_soundness
    (f : ZkVec p n → ZMod p)
    (ε : ℝ)
    (hfar : epsilon_far_from_linear_normalized f ε) :
    BLR_accept_prob f
      ≤
      1 -
      (((p : ℝ) - 1) / p) *
        (1 - Real.cos (2 * Real.pi / p)) * ε := by
  rw [BLR_accept_prob_eq_fourier_sum];
  -- Separate the j = 0 term from the rest.
  rw [ Finset.sum_eq_add_sum_diff_singleton ( Finset.mem_univ 0 ) ];
  -- Bound: j=0 contributes 1, each j≠0 contributes ≤ 1 − (1−cos)ε.
  refine' le_trans ( mul_le_mul_of_nonneg_left ( add_le_add ( le_of_eq <| lift_omega_j_zero_contribution f ) <| Finset.sum_le_sum fun x hx => weighted_sum_lift_omega_j_bound f ε hfar x <| by aesop ) <| by positivity ) _;
  -- Simplify the arithmetic: (1/p)(1 + (p−1)(1−cε)) = 1 − ((p−1)/p)cε.
  norm_num [ Finset.card_sdiff, Finset.card_singleton, Finset.card_univ, ZMod.card ];
  rw [ Nat.cast_pred ( Nat.Prime.pos Fact.out ) ] ; ring_nf ; norm_num [ Nat.Prime.ne_zero Fact.out ]

end BLR_TEST_SOUNDNESS_PRIME

-- ============================================================================
-- SECTION 8: BLR_TEST_SOUNDNESS_GENERAL
-- ----------------------------------------------------------------------------
-- This section extends the BLR soundness theorem from prime fields to
-- arbitrary moduli k ≥ 2. The main difference is that when k is composite,
-- not every nonzero j ∈ ℤ_k is a unit: the multiplication-by-j trick only
-- works when j is invertible.
--
-- The solution is to split ∑_{j ∈ ℤ_k} into:
--   • Units (j ∈ (ℤ/kℤ)×): use the Fourier bound ≤ 1 − (1−cos(2π/k))ε
--     (exactly as in the prime case, via the multiplication-by-j trick).
--   • Non-units: use the trivial Parseval bound ≤ 1.
--
-- This gives:
--   Pr[accept] = (1/k)[1 + φ(k)·(1 − (1−cos)ε) + (k − 1 − φ(k))·1]
--             ≤ 1 − (φ(k)/k)(1 − cos(2π/k))ε
-- where φ(k) = Euler's totient = |(ℤ/kℤ)×| is the number of units.
-- When k = p is prime, φ(p) = p − 1, recovering the prime-field result.
-- ============================================================================
section BLR_TEST_SOUNDNESS_GENERAL

variable {k : ℕ} [NeZero k] {n : ℕ}


-- Multiplication by a unit preserves distance from linearity.
lemma unit_mul_epsilon_far
    (f : ZkVec k n → ZMod k)
    (ε : ℝ)
    (hfar : epsilon_far_from_linear_normalized f ε)
    (j : (ZMod k)ˣ) :
    epsilon_far_from_linear_normalized (fun x => (j : ZMod k) * f x) ε := by
  obtain ⟨hf₁, hf₂, hf₃, hf₄⟩ := hfar;
  refine' ⟨ _, hf₂, hf₃, fun g hg => _ ⟩;
  -- Normalization: j · f(0) = j · 0 = 0.
  · exact mul_eq_zero_of_right _ hf₁;
  -- Distance preservation: dist(j·f, g) = dist(f, j⁻¹·g).
  · convert hf₄ ( fun x => j⁻¹ * g x ) _ using 1;
    · unfold zk_dist;
      congr! 2;
      split_ifs <;> simp_all +decide [ mul_comm ];
      · exact ‹¬f _ = g _ * ↑j⁻¹› ( by rw [ ← ‹↑j * f _ = g _›, mul_right_comm, Units.mul_inv, one_mul ] );
      · simp_all +decide [ mul_left_comm ( j : ZMod k ), Units.mul_inv ];
    -- j⁻¹ · g is linear if g is linear.
    · intro x y; simp +decide [ hg x y, mul_add ] ;

-- For a unit `j`, if `f` is ε-far from linear, then `Re[f̂_j(s)] ≤ 1 − (1 − cos(2π/k))ε`.
lemma re_fourier_coeff_lift_omega_j_unit_bound
    (hk : 2 ≤ k)
    (f : ZkVec k n → ZMod k)
    (ε : ℝ)
    (hfar : epsilon_far_from_linear_normalized f ε)
    (j : (ZMod k)ˣ)
    (s : ZkVec k n) :
    (fourier_coeff (lift_omega_j (↑j) f) s).re
      ≤ 1 - (1 - Real.cos (2 * Real.pi / k)) * ε := by
  -- Set g(x) = j·f(x). By unit_mul_epsilon_far, g is ε-far from linear.
  set g : ZkVec k n → ZMod k := fun x => (j : ZMod k) * f x;
  have hg : epsilon_far_from_linear_normalized g ε := unit_mul_epsilon_far f ε hfar j;
  convert re_epsilon_far_bounds_fourier hk g ε hg s using 1

-- For a unit `j`, if `f` is ε-far from linear, the weighted Fourier sum is at most `1 − (1 − cos(2π/k))ε`.
lemma weighted_sum_unit_bound
    (hk : 2 ≤ k)
    (f : ZkVec k n → ZMod k)
    (ε : ℝ)
    (hfar : epsilon_far_from_linear_normalized f ε)
    (j : (ZMod k)ˣ) :
    ∑ s : ZkVec k n,
      ‖fourier_coeff (lift_omega_j (↑j) f) s‖ ^ 2 *
        (fourier_coeff (lift_omega_j (↑j) f) s).re
      ≤ 1 - (1 - Real.cos (2 * Real.pi / k)) * ε := by
  -- Apply the per-coefficient bound for units.
  have h_coeff_unit_bound : ∀ s : ZkVec k n, (fourier_coeff (lift_omega_j (↑j) f) s).re ≤ 1 - (1 - Real.cos (2 * Real.pi / k)) * ε := by
    exact fun s => re_fourier_coeff_lift_omega_j_unit_bound hk f ε hfar j s
  -- Multiply by |f̂_j(s)|² ≥ 0 and sum.
  refine' le_trans ( Finset.sum_le_sum fun s _ => mul_le_mul_of_nonneg_left ( h_coeff_unit_bound s ) ( sq_nonneg _ ) ) _;
  -- Factor out the constant and apply Parseval.
  rw [ ← Finset.sum_mul _ _ _, parseval_lift_omega_j ] ; norm_num

/-
If `f : ℤ_k^n → ℤ_k` is ε-far from every
linear function, then `Pr[BLR accepts f] ≤ 1 − (φ(k)/k)(1 − cos(2π/k))ε`.
When `k = p` is prime, `φ(p) = p − 1` and this recovers the prime-field bound
`1 − ((p−1)/p)(1 − cos(2π/p))ε`. For general `k`, the constant `φ(k)/k`
captures the fraction of units in `ℤ_k`, which controls how many
multiplication-by-`j` arguments are available in the Fourier analysis.
-/
lemma BLR_soundness_general
    (hk : 2 ≤ k)
    (f : ZkVec k n → ZMod k)
    (ε : ℝ)
    (hfar : epsilon_far_from_linear_normalized f ε) :
    BLR_accept_prob f
      ≤ 1 - ((Nat.totient k : ℝ) / k) *
          (1 - Real.cos (2 * Real.pi / k)) * ε := by
  rw [ BLR_accept_prob_eq_fourier_sum ];
  rw [ div_mul_eq_mul_div, div_le_iff₀ ];
  · -- Split the sum over j into units and non-units.
    have h_split_sum : ∑ j : ZMod k, ∑ s : ZkVec k n, ‖fourier_coeff (lift_omega_j j f) s‖ ^ 2 * (fourier_coeff (lift_omega_j j f) s).re =
      ∑ j ∈ Finset.filter IsUnit (Finset.univ : Finset (ZMod k)), ∑ s : ZkVec k n, ‖fourier_coeff (lift_omega_j j f) s‖ ^ 2 * (fourier_coeff (lift_omega_j j f) s).re +
      ∑ j ∈ Finset.filter (fun j => ¬IsUnit j) (Finset.univ : Finset (ZMod k)), ∑ s : ZkVec k n, ‖fourier_coeff (lift_omega_j j f) s‖ ^ 2 * (fourier_coeff (lift_omega_j j f) s).re := by
        rw [ Finset.sum_filter_add_sum_filter_not ];
    -- Bound the unit part: φ(k) terms, each ≤ 1 − (1−cos)ε.
    have h_unit_bound : ∑ j ∈ Finset.filter IsUnit (Finset.univ : Finset (ZMod k)), ∑ s : ZkVec k n, ‖fourier_coeff (lift_omega_j j f) s‖ ^ 2 * (fourier_coeff (lift_omega_j j f) s).re ≤ (k.totient : ℝ) * (1 - (1 - Real.cos (2 * Real.pi / k)) * ε) := by
      have h_units_bound : ∀ j : (ZMod k)ˣ, ∑ s : ZkVec k n, ‖fourier_coeff (lift_omega_j (↑j) f) s‖ ^ 2 * (fourier_coeff (lift_omega_j (↑j) f) s).re ≤ 1 - (1 - Real.cos (2 * Real.pi / k)) * ε := by
        exact fun j => weighted_sum_unit_bound hk f ε hfar j;
      -- Reindex the sum over units to a sum over (ZMod k)ˣ.
      convert Finset.sum_le_sum fun j ( hj : j ∈ Finset.univ ) => h_units_bound j;
      · refine' Finset.sum_bij ( fun x hx => Units.mkOfMulEqOne x ( Classical.choose ( isUnit_iff_exists_inv.mp ( by simpa using hx ) ) ) ( Classical.choose_spec ( isUnit_iff_exists_inv.mp ( by simpa using hx ) ) ) ) _ _ _ _ <;> simp +decide [ Units.ext_iff ];
      · norm_num;
        ring;
    -- Bound the non-unit part: (k − φ(k)) terms, each ≤ 1.
    have h_nonunit_bound : ∑ j ∈ Finset.filter (fun j => ¬IsUnit j) (Finset.univ : Finset (ZMod k)), ∑ s : ZkVec k n, ‖fourier_coeff (lift_omega_j j f) s‖ ^ 2 * (fourier_coeff (lift_omega_j j f) s).re ≤ (k - k.totient : ℝ) := by
      refine' le_trans ( Finset.sum_le_sum fun x hx => weighted_fourier_sum_le_one x f ) _ ; norm_num [ Finset.filter_not, Finset.card_sdiff ];
      rw [ Nat.cast_sub ];
      -- The number of units equals φ(k), and the total count is k.
      · rw [ show ( Finset.filter IsUnit Finset.univ : Finset ( ZMod k ) ) = Finset.image ( fun x : ( ZMod k )ˣ => x.val ) Finset.univ from ?_, Finset.card_image_of_injective _ fun x y hxy => by simpa [ Units.ext_iff ] using hxy ] ; norm_num [ ZMod.card_units_eq_totient ];
        ext; simp [IsUnit];
      · exact le_trans ( Finset.card_filter_le _ _ ) ( by simp +decide [ Finset.card_univ ] );
    -- Combine the two bounds and simplify the arithmetic.
    rw [ div_mul_eq_mul_div, div_mul_eq_mul_div, sub_div', div_mul_cancel₀ ] <;> first | positivity | nlinarith;
  · positivity

/-
For prime `k = p`, the general bound specializes to the original:
`Pr[BLR accepts] ≤ 1 − ((p−1)/p)(1 − cos(2π/p))ε`.
-/
lemma BLR_soundness_prime
    {p : ℕ} [Fact p.Prime]
    (f : ZkVec p n → ZMod p)
    (ε : ℝ)
    (hfar : epsilon_far_from_linear_normalized f ε) :
    BLR_accept_prob f
      ≤ 1 - (((p : ℝ) - 1) / p) *
          (1 - Real.cos (2 * Real.pi / p)) * ε := by
  convert BLR_soundness_general _ f ε hfar using 3;
  -- φ(p) = p − 1 for prime p.
  · rw [ Nat.totient_prime Fact.out ];
    rw [ Nat.cast_pred ( Nat.Prime.pos Fact.out ) ];
  · exact Nat.Prime.two_le Fact.out

end BLR_TEST_SOUNDNESS_GENERAL

end ZkBLR
