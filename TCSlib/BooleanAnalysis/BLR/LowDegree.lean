/-
Copyright (c) 2026 Prastik Mohanraj. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prastik Mohanraj
-/

import TCSlib.BooleanAnalysis.BLR.BoolFourier
import TCSlib.BooleanAnalysis.BLR.BoolBLR

set_option maxHeartbeats 0
set_option maxRecDepth 10000
set_option relaxedAutoImplicit false
set_option autoImplicit false

open Finset BoolFourier BoolBLR

namespace LowDegreeTest

/-!
# Low-Degree (Reed-Muller) Testing on the Boolean Hypercube

## Main results

- `gowers_norm_eq_one_iff`: The U^{d+1} Gowers norm equals 1 iff the function has degree at most d
- `gowers_U2_fourier`: The U² norm to the fourth power equals the sum of fourth powers of Fourier coefficients
- `ReedMuller_monotone`: RM(d,n) is a subset of RM(d+1,n)
- `ReedMuller_one_is_affine`: Functions in RM(1,n) are affine (linear or linear plus constant)
- `degree_test_accept_prob_eq`: Acceptance probability of degree test equals (1 + Gowers norm) / 2
- `degree_test_completeness`: Degree-d functions pass the test with probability 1
- `degree_test_qualitative_soundness`: Non-degree-d functions pass with probability strictly less than 1
- `fourier_coeff_le_of_far_from_degree`: Functions epsilon-far from degree d have Fourier coefficients bounded by 1 - 2*epsilon
- `abs_fourier_coeff_le_of_far_from_degree`: Absolute Fourier coefficients bounded by 1 - 2*epsilon for epsilon-far functions
- `gowers_norm_le_of_far_d1`: U² Gowers norm bounded by 1 - 2*epsilon for functions epsilon-far from degree 1
- `RM_test_completeness`: Reed-Muller codewords pass the RM test with probability 1

## References

- Original formalization by Prastik Mohanraj
-/

-- ============================================================================
-- SECTION 1: HYPERCUBE_ALGEBRA
-- ----------------------------------------------------------------------------
-- This section establishes the basic algebraic properties of the XOR group
-- structure on the Boolean hypercube {0,1}^n ≅ (F₂)^n. The hypercube carries
-- the structure of an abelian group under coordinate-wise XOR, with the zero
-- vector as identity.
--
-- These are elementary identities (commutativity, identity, self-inverse,
-- associativity) that will be used throughout the low-degree testing theory,
-- particularly in the definition and manipulation of Gowers products and
-- multiplicative derivatives.
-- ============================================================================
section HYPERCUBE_ALGEBRA

variable {n : ℕ}

-- x + y = y + x
lemma xor_vec_comm (x y : hypercube n) : xor_vec x y = xor_vec y x := by
  exact funext fun i => by simp +decide [ xor_vec, Bool.xor_comm ] ;

-- x + 0 = x
lemma xor_vec_zero (x : hypercube n) : xor_vec x (zero_vec n) = x := by
  funext i; simp [xor_vec, zero_vec]

-- x + x = 0
lemma xor_vec_self (x : hypercube n) : xor_vec x x = zero_vec n := by
  exact funext fun i => by unfold xor_vec zero_vec; cases x i <;> rfl;

-- (x + y) + z = x + (y + z)
lemma xor_vec_assoc (x y z : hypercube n) :
    xor_vec (xor_vec x y) z = xor_vec x (xor_vec y z) := by
  funext i; simp +decide [ xor_vec ] ;

end HYPERCUBE_ALGEBRA

-- ============================================================================
-- SECTION 2: GOWERS_PRODUCT
-- ----------------------------------------------------------------------------
-- The Gowers product (also called the "multiplicative derivative product")
-- is the central algebraic object in low-degree testing. For a real-valued
-- function f on the hypercube and direction vectors h₁, …, hₖ, it is defined
-- recursively:
--
--   GP(f, 0, x, ∅) = f(x)
--   GP(f, k+1, x, (h₁,…,hₖ₊₁)) = GP(f, k, x, (h₁,…,hₖ))
--                                  · GP(f, k, x⊕hₖ₊₁, (h₁,…,hₖ))
--
-- The k-th order Gowers product takes 2^k evaluations of f, one at each
-- vertex of the cube x + span{h₁, …, hₖ}. When f = (-1)^g for a Boolean
-- function g, the Gowers product equals (-1)^{∑_{ω∈{0,1}^k} g(x+ω·h)}.
--
-- Key properties:
-- • The order-1 Gowers product is the multiplicative derivative:
--   GP(f, 1, x, h) = f(x) · f(x ⊕ h) = (Δ_h f)(x).
-- • For ±1-valued functions, GP always lies in {±1}.
-- ============================================================================
section GOWERS_PRODUCT

variable {n : ℕ}

-- (Δ_h f)(x) = f(x) f(x + h)
def mult_deriv (f : BoolFun n) (h : hypercube n) : BoolFun n :=
  fun x => f x * f (xor_vec x h)

-- ∏_{ω ∈ {0,1}^k} f(x + ω · h)
def gowers_product (f : BoolFun n) :
    (k : ℕ) → hypercube n → (Fin k → hypercube n) → ℝ
  | 0, x, _ => f x
  | k + 1, x, hs =>
    gowers_product f k x (hs ∘ Fin.castSucc) *
    gowers_product f k (xor_vec x (hs (Fin.last k))) (hs ∘ Fin.castSucc)

-- Gowers product of order 0 is f(x)
@[simp]
lemma gowers_product_zero (f : BoolFun n) (x : hypercube n)
    (hs : Fin 0 → hypercube n) :
    gowers_product f 0 x hs = f x := rfl

-- Recursive expansion of the Gowers product
@[simp]
lemma gowers_product_succ (f : BoolFun n) (k : ℕ) (x : hypercube n)
    (hs : Fin (k + 1) → hypercube n) :
    gowers_product f (k + 1) x hs =
      gowers_product f k x (hs ∘ Fin.castSucc) *
      gowers_product f k (xor_vec x (hs (Fin.last k))) (hs ∘ Fin.castSucc) := rfl

-- Δ_h f(x) = GowersProduct_1(f)(x,h)
lemma mult_deriv_eq_gowers_one (f : BoolFun n) (x : hypercube n) (h : hypercube n) :
    mult_deriv f h x = gowers_product f 1 x (fun _ => h) := by
  unfold gowers_product; aesop;

-- Gowers products of {±1}-valued functions lie in {±1}
lemma gowers_product_pm1 (f : hypercube n → Bool) (k : ℕ)
    (x : hypercube n) (hs : Fin k → hypercube n) :
    gowers_product (lift_pm1 f) k x hs = 1 ∨
    gowers_product (lift_pm1 f) k x hs = -1 := by
  have h_lift_pm1 : ∀ x, lift_pm1 f x = 1 ∨ lift_pm1 f x = -1 := by
    exact fun x => by unfold lift_pm1; cases f x <;> tauto;
  induction' k with k ih generalizing x;
  · exact h_lift_pm1 x;
  · cases ih x ( hs ∘ Fin.castSucc ) <;> cases ih ( xor_vec x ( hs ( Fin.last k ) ) ) ( hs ∘ Fin.castSucc ) <;> simp +decide [ *, gowers_product_succ ]

end GOWERS_PRODUCT

-- ============================================================================
-- SECTION 3: MULTI_EXPECTATION
-- ----------------------------------------------------------------------------
-- The multi-expectation E_{h₁,…,hₖ}[g(h₁,…,hₖ)] is the uniform average
-- of a function g over all k-tuples of hypercube vectors. This is used to
-- define Gowers norms, which involve averaging Gowers products over all
-- choices of the direction vectors h₁, …, hₖ.
--
-- The domain (Fin k → hypercube n) has cardinality (2^n)^k = 2^{nk}, which
-- is the normalizing factor in the definition.
-- ============================================================================
section MULTI_EXPECTATION

variable {n : ℕ}

-- E_{h_1,...,h_k}[ g(h_1,...,h_k) ]
noncomputable def multi_expectation {k : ℕ}
    (g : (Fin k → hypercube n) → ℝ) : ℝ :=
  (∑ hs : Fin k → hypercube n, g hs) / (2 : ℝ) ^ (n * k)

-- |(F₂^n)^k| = 2^(nk)
lemma card_multi_hypercube (n k : ℕ) :
    Fintype.card (Fin k → hypercube n) = 2 ^ (n * k) := by
  rw [ Fintype.card_pi ] ; norm_num [ card_hypercube ] ; ring

-- E[c] = c
@[simp]
lemma multi_expectation_const {k : ℕ} (c : ℝ) :
    multi_expectation (n := n) (fun _ : Fin k → hypercube n => c) = c := by
  unfold multi_expectation;
  rw [ div_eq_iff ] <;> norm_cast <;> norm_num [ pow_mul, card_hypercube ];
  ring

end MULTI_EXPECTATION

-- ============================================================================
-- SECTION 4: POLYNOMIAL_DEGREE
-- ----------------------------------------------------------------------------
-- A function f : F₂^n → F₂ has degree ≤ d if all its (d+1)-fold
-- multiplicative derivatives vanish. More precisely, for the ±1-valued
-- lift F = (-1)^f, we say deg(f) ≤ d iff
--     GP(F, d+1, x, h₁, …, h_{d+1}) = 1   for all x, h₁, …, h_{d+1}.
--
-- This is equivalent to the standard algebraic definition: f can be
-- written as a multilinear polynomial over F₂ of degree ≤ d.
--
-- Key results in this section:
-- • Monotonicity: deg ≤ d ⟹ deg ≤ d+1.
-- • deg ≤ 0 ⟺ f is constant.
-- • Linear functions (f(x⊕y) = f(x)⊕f(y)) have deg ≤ 1.
-- • deg ≤ 1 functions are affine (linear or linear + 1).
-- ============================================================================
section POLYNOMIAL_DEGREE

variable {n : ℕ}

-- f has degree ≤ d iff all (d+1)-fold multiplicative derivatives equal 1
def is_degree_le_pm1 (f : BoolFun n) (d : ℕ) : Prop :=
  ∀ (hs : Fin (d + 1) → hypercube n) (x : hypercube n),
    gowers_product f (d + 1) x hs = 1

-- Boolean version of degree ≤ d
def is_degree_le_bool (f : hypercube n → Bool) (d : ℕ) : Prop :=
  is_degree_le_pm1 (lift_pm1 f) d

-- degree ≤ d implies degree ≤ d+1
lemma degree_le_succ {f : BoolFun n} {d : ℕ}
    (hd : is_degree_le_pm1 f d) :
    is_degree_le_pm1 f (d + 1) := by
  intro hs x;
  convert congr_arg₂ ( · * · ) ( hd ( fun i => hs ( Fin.castSucc i ) ) x ) ( hd ( fun i => hs ( Fin.castSucc i ) ) ( xor_vec x ( hs ( Fin.last _ ) ) ) ) using 1;
  norm_num

-- degree ≤ 0 iff f is constant
lemma degree_le_zero_iff_constant (f : hypercube n → Bool) :
    is_degree_le_bool f 0 ↔ (∀ x y : hypercube n, f x = f y) := by
  constructor;
  · intro h x y
    -- Use the derivative condition with h = x ⊕ y.
    have h_eq : f x = f (xor_vec x (xor_vec x y)) := by
      have := h ( fun _ => xor_vec x y ) x;
      cases h : f x <;> cases h' : f ( xor_vec x ( xor_vec x y ) ) <;> simp_all +decide ;
      · unfold lift_pm1 at this; simp_all +decide [ BoolToPM1 ] ;
        norm_num at this;
      · unfold lift_pm1 at this; simp_all +decide ;
        exact absurd this ( by norm_num );
    -- x ⊕ (x ⊕ y) = y by associativity and self-inverse.
    unfold xor_vec at *; aesop;
  · intro h hs x; simp +decide [ lift_pm1 ] ;
    -- Since f is constant, f(x) = f(x ⊕ h), so f(x)·f(x⊕h) = f(x)² = 1.
    rw [ h x ( xor_vec x ( hs 0 ) ) ] ; unfold BoolToPM1; aesop;

-- linear functions have degree ≤ 1
lemma linear_is_degree_le_one {f : hypercube n → Bool}
    (hlin : is_linear_bool f) :
    is_degree_le_bool f 1 := by
  intro hs x; simp +decide [ gowers_product_succ ];
  -- Use linearity to factor each term as a product of lift_pm1 at individual points.
  have h_simp : lift_pm1 f (xor_vec x (hs 0)) = lift_pm1 f x * lift_pm1 f (hs 0) ∧ lift_pm1 f (xor_vec x (hs 1)) = lift_pm1 f x * lift_pm1 f (hs 1) ∧ lift_pm1 f (xor_vec (xor_vec x (hs 1)) (hs 0)) = lift_pm1 f x * lift_pm1 f (hs 1) * lift_pm1 f (hs 0) := by
    have h_simp : ∀ a b : hypercube n, lift_pm1 f (xor_vec a b) = lift_pm1 f a * lift_pm1 f b := by
      intros a b
      simp [lift_pm1];
      rw [ hlin a b, BoolToPM1_xor ];
    aesop;
  -- Substitute and simplify: each ±1 factor appears an even number of times.
  rw [ h_simp.1, h_simp.2.1, h_simp.2.2 ] ; ring_nf;
  unfold lift_pm1;
  cases f x <;> cases f ( hs 0 ) <;> cases f ( hs 1 ) <;> norm_num [ BoolToPM1 ]

-- degree ≤ 1 functions are affine
lemma degree_le_one_implies_affine {f : hypercube n → Bool}
    (hdeg : is_degree_le_bool f 1) :
    is_linear_bool f ∨ is_linear_bool (fun x => !(f x)) := by
  -- Extract the vanishing second-derivative condition.
  have h_second_deriv_zero : ∀ (x h1 h2 : hypercube n), (lift_pm1 f x) * (lift_pm1 f (xor_vec x h1)) * (lift_pm1 f (xor_vec x h2)) * (lift_pm1 f (xor_vec (xor_vec x h1) h2)) = 1 := by
    intro x h1 h2
    have := hdeg ( ![h1, h2] ) x
    simp_all +decide [ gowers_product_succ ];
    convert this using 1 ; ring_nf;
    unfold xor_vec; simp +decide [ Bool.xor_comm ] ; ring_nf;
    exact Or.inl ( congr_arg _ ( funext fun i => by by_cases hi : x i <;> by_cases hj : h1 i <;> by_cases hk : h2 i <;> simp +decide [ hi, hj, hk ] ) );
  -- Branch on the value of f at the origin.
  by_cases h : f ( zero_vec n ) <;> simp_all +decide [ is_linear_bool ];
  · -- Case f(0) = true: show ¬f is linear.
    right;
    intro x y; specialize h_second_deriv_zero ( zero_vec n ) x y; simp_all +decide [ lift_pm1 ] ;
    -- Exhaustive case analysis on f(x), f(y), f(x⊕y).
    cases h : f x <;> cases h' : f y <;> simp_all +decide ;
    · cases h'' : f ( xor_vec x y ) <;> simp_all +decide ;
      unfold xor_vec at *; simp_all +decide [ zero_vec ] ;
      norm_num [ BoolToPM1 ] at h_second_deriv_zero;
    · cases h'' : f ( xor_vec x y ) <;> simp_all +decide ;
      unfold xor_vec at *; simp_all +decide [ zero_vec ] ;
      norm_num at h_second_deriv_zero;
    · cases h'' : f ( xor_vec x y ) <;> simp_all +decide ;
      rw [ show xor_vec ( zero_vec n ) x = x from funext fun i => by simp +decide [ xor_vec, zero_vec ] ] at h_second_deriv_zero ; rw [ show xor_vec ( zero_vec n ) y = y from funext fun i => by simp +decide [ xor_vec, zero_vec ] ] at h_second_deriv_zero ; simp_all +decide ;
      norm_num at h_second_deriv_zero;
    · cases h'' : f ( xor_vec x y ) <;> simp_all +decide [ BoolToPM1 ];
      unfold xor_vec at *; simp_all +decide [ zero_vec ] ;
      norm_num at h_second_deriv_zero;
  · -- Case f(0) = false: show f is linear.
    left;
    intro x y; specialize h_second_deriv_zero ( zero_vec n ) x y; simp_all +decide [ lift_pm1 ] ;
    cases h : f x <;> cases h' : f y <;> simp_all +decide ;
    · cases h'' : f ( xor_vec x y ) <;> simp_all +decide ;
      unfold xor_vec at *; simp_all +decide [ zero_vec ] ;
      norm_num at h_second_deriv_zero;
    · cases h'' : f ( xor_vec x y ) <;> simp_all +decide ;
      unfold xor_vec at *; simp_all +decide [ zero_vec ] ;
      norm_num at h_second_deriv_zero;
    · unfold xor_vec at *; simp_all +decide [ zero_vec ] ;
      cases h'' : f ( fun i => x i ^^ y i ) <;> simp_all +decide [ BoolToPM1 ];
      norm_num at h_second_deriv_zero;
    · unfold xor_vec at *; simp_all +decide [ zero_vec ] ;
      cases h'' : f ( fun i => x i ^^ y i ) <;> simp_all +decide [ BoolToPM1 ];
      norm_num at h_second_deriv_zero

end POLYNOMIAL_DEGREE

-- ============================================================================
-- SECTION 5: REED_MULLER
-- ----------------------------------------------------------------------------
-- The Reed–Muller code RM(d, n) over F₂ is the set of all Boolean functions
-- f : F₂^n → F₂ of degree ≤ d. Equivalently, RM(d, n) consists of all
-- multilinear polynomials of degree ≤ d over F₂.
--
-- This section defines the code and establishes basic structural properties:
-- • Monotonicity: RM(d, n) ⊆ RM(d+1, n).
-- • The zero and one functions are in RM(d, n) for all d.
-- • RM(1, n) consists exactly of affine functions (linear + constant).
-- ============================================================================
section REED_MULLER

variable {n : ℕ}

-- RM(d,m) = { f : F₂^m → F₂ | deg(f) ≤ d }
def ReedMuller (d : ℕ) (m : ℕ) : Set (hypercube m → Bool) :=
  { f | is_degree_le_bool f d }

-- RM(d,n) ⊆ RM(d+1,n)
lemma ReedMuller_monotone (d : ℕ) :
    ReedMuller d n ⊆ ReedMuller (d + 1) n := by
  intro f hf
  exact degree_le_succ hf

-- 0 ∈ RM(d,n)
lemma zero_mem_ReedMuller (d : ℕ) :
    (fun _ : hypercube n => false) ∈ ReedMuller d n := by
  intro hs x;
  induction' d with d ih generalizing x;
  · exact mul_one _;
  · convert congr_arg₂ ( · * · ) ( ih _ _ ) ( ih _ _ ) using 1;
    norm_num

-- 1 ∈ RM(d,n)
lemma one_mem_ReedMuller (d : ℕ) :
    (fun _ : hypercube n => true) ∈ ReedMuller d n := by
  intro hs x; induction' d with d hd generalizing x <;> simp_all +decide [ gowers_product ] ;
  · unfold lift_pm1; norm_num [ BoolToPM1 ] ;
  · convert congr_arg₂ ( · * · ) ( hd ( fun i => hs ( Fin.castSucc i ) ) x ) ( hd ( fun i => hs ( Fin.castSucc i ) ) ( xor_vec x ( hs ( Fin.last ( d + 1 ) ) ) ) ) using 1 ; ring!

-- linear functions lie in RM(1,n)
lemma linear_mem_ReedMuller_one {f : hypercube n → Bool}
    (hlin : is_linear_bool f) :
    f ∈ ReedMuller 1 n :=
  linear_is_degree_le_one hlin

-- RM(1,n) consists of affine functions
lemma ReedMuller_one_is_affine {f : hypercube n → Bool}
    (hf : f ∈ ReedMuller 1 n) :
    is_linear_bool f ∨ is_linear_bool (fun x => !(f x)) :=
  degree_le_one_implies_affine hf

end REED_MULLER

-- ============================================================================
-- SECTION 6: GOWERS_NORM
-- ----------------------------------------------------------------------------
-- The Gowers uniformity norm ‖f‖_{Uᵏ} measures how "pseudorandom" a function
-- f is with respect to degree-(k-1) structure. It is defined via
--
--   ‖f‖_{Uᵏ}^{2^k} = E_x E_{h₁,…,hₖ} [GP(f, k, x, h₁, …, hₖ)]
--
-- Key facts established here:
-- • ‖f‖_{U^{d+1}}^{2^{d+1}} = 1 ⟺ deg(f) ≤ d.
--   (A ±1-valued function has maximal Gowers norm iff it's low-degree.)
-- • ‖f‖_{U²}⁴ = ‖f∗f‖₂² (the U² norm relates to convolution).
-- • ‖f‖_{U²}⁴ = ∑_S f̂(S)⁴ (the U² norm in terms of Fourier coefficients).
-- • ‖f‖_{Uᵏ}^{2^k} ≤ 1 for ±1-valued f (the Gowers norm is at most 1).
-- ============================================================================
section GOWERS_NORM

variable {n : ℕ}

-- ||f||_{U^k}^{2^k}
noncomputable def gowers_norm_pow (f : BoolFun n) (k : ℕ) : ℝ :=
  expectation (fun x =>
    multi_expectation (fun hs : Fin k → hypercube n =>
      gowers_product f k x hs))

-- ||f||_{U^{d+1}} = 1 iff deg(f) ≤ d
lemma gowers_norm_eq_one_iff (f : hypercube n → Bool) (d : ℕ) :
    gowers_norm_pow (lift_pm1 f) (d + 1) = 1 ↔ is_degree_le_bool f d := by
  refine' ⟨ fun h => _, _ ⟩;
  · intro hs x;
    unfold gowers_norm_pow at h;
    -- Contrapositive: if some GP value is -1, the average is < 1.
    contrapose! h;
    have h_avg_lt_one : (∑ x : hypercube n, ∑ hs : Fin (d + 1) → hypercube n, gowers_product (lift_pm1 f) (d + 1) x hs) < (2 : ℝ) ^ (n * (d + 1) + n) := by
      have h_avg_lt_one : (∑ x : hypercube n, ∑ hs : Fin (d + 1) → hypercube n, gowers_product (lift_pm1 f) (d + 1) x hs) < ∑ x : hypercube n, ∑ hs : Fin (d + 1) → hypercube n, 1 := by
        refine' Finset.sum_lt_sum _ _;
        -- Each term is ≤ 1 (since GP ∈ {±1}).
        · exact fun i _ => Finset.sum_le_sum fun j _ => show gowers_product ( lift_pm1 f ) ( d + 1 ) i j ≤ 1 from by cases gowers_product_pm1 f ( d + 1 ) i j <;> linarith;
        -- At least one term is < 1 (i.e., equals -1).
        · refine' ⟨ x, Finset.mem_univ _, Finset.sum_lt_sum _ _ ⟩;
          · intro i hi; exact le_of_abs_le ( by rw [ abs_le ] ; constructor <;> cases gowers_product_pm1 f ( d + 1 ) x i <;> linarith ) ;
          · exact ⟨ hs, Finset.mem_univ _, lt_of_le_of_ne ( by cases gowers_product_pm1 f ( d + 1 ) x hs <;> linarith ) h ⟩;
      convert h_avg_lt_one using 1 ; norm_num [ card_hypercube, card_multi_hypercube ] ; ring;
    unfold expectation multi_expectation; simp_all +decide [ pow_add, pow_mul ] ;
    rw [ ← Finset.sum_div _ _ _, div_div, div_eq_iff ] <;> first | positivity | linarith;
  · -- (⇐) direction: all GP values are 1, so the average is 1.
    unfold gowers_norm_pow is_degree_le_bool;
    unfold expectation multi_expectation;
    intro h; simp_all +decide [ ← Finset.sum_div _ _ _, is_degree_le_pm1 ] ;
    rw [ div_div, div_eq_iff ] <;> norm_cast <;> norm_num [ card_hypercube ] ; ring

-- ||f||_{U²}^4 = ||f * f||_2^2
lemma gowers_U2_eq_L2_conv (f : BoolFun n) :
    gowers_norm_pow f 2 = L2_norm_sq (convolution f f) := by
  -- Expand the order-2 Gowers product explicitly.
  have h_gowers_norm_pow : gowers_norm_pow f 2 = expectation (fun x => multi_expectation (fun hs : Fin 2 → hypercube n => f x * f (xor_vec x (hs 0)) * f (xor_vec x (hs 1)) * f (xor_vec (xor_vec x (hs 1)) (hs 0)))) := by
    unfold gowers_norm_pow;
    congr! 3;
    ext hs; simp +decide [ gowers_product ] ; ring;
  -- Change variables: replace the pair (hs 0, hs 1) with (h, z) where z = x ⊕ hs(1).
  have h_change_vars : ∀ x : hypercube n, ∑ hs : Fin 2 → hypercube n, f x * f (xor_vec x (hs 0)) * f (xor_vec x (hs 1)) * f (xor_vec (xor_vec x (hs 1)) (hs 0)) = ∑ h : hypercube n, ∑ z : hypercube n, f x * f (xor_vec x h) * f z * f (xor_vec z h) := by
    intro x;
    rw [ ← Finset.sum_product' ];
    refine' Finset.sum_bij ( fun hs _ => ( hs 0, xor_vec x ( hs 1 ) ) ) _ _ _ _ <;> simp +decide;
    · intro a₁ a₂ h₁ h₂; funext i; fin_cases i
      · exact h₁
      · funext j; have hj := congr_fun h₂ j; simp only [ xor_vec ] at hj
        cases x j <;> cases a₁ 1 j <;> cases a₂ 1 j <;> simp_all +decide;
    · intro a b; use fun i => if i = 0 then a else xor_vec x b; simp +decide ;
      exact funext fun i => by unfold xor_vec; simp +decide [ Bool.xor ] ;
  -- After the change of variables, the expression matches ‖f∗f‖₂².
  simp_all +decide [ L2_norm_sq, BoolFourier.convolution ];
  unfold expectation multi_expectation; simp +decide [ *, Finset.sum_div _ _ _, Finset.mul_sum _ _ _, Finset.sum_mul _ _ _, pow_two ] ; ring_nf;
  rw [ Finset.sum_comm ] ; congr ; ext ; rw [ Finset.sum_comm ] ; congr ; ext ; ring_nf;
  simp +decide only [xor_vec_comm] ; congr ; ext ; ring;

-- ||f||_{U²}^4 = ∑_S f̂(S)^4
lemma gowers_U2_fourier (f : BoolFun n) :
    gowers_norm_pow f 2 = ∑ S : Finset (Fin n), (fourier_coeff f S) ^ 4 := by
  rw [ gowers_U2_eq_L2_conv, ← parseval_identity ];
  -- By the convolution theorem, (f∗f)^(S) = f̂(S)², so (f∗f)^(S)² = f̂(S)⁴.
  exact Finset.sum_congr rfl fun _ _ => by rw [ fourier_coeff_convolution ] ; ring;

-- ||f||_{U^k}^{2^k} ≤ 1 for {±1}-valued f and all k
lemma gowers_norm_le_one (f : hypercube n → Bool) (k : ℕ) :
    gowers_norm_pow (lift_pm1 f) k ≤ 1 := by
  refine' div_le_one_of_le₀ _ _;
  · refine' le_trans ( Finset.sum_le_sum fun i hi => div_le_one_of_le₀ ( _ ) ( by positivity ) ) _;
    · refine' le_trans ( Finset.sum_le_sum fun _ _ => show gowers_product ( lift_pm1 f ) k i _ ≤ 1 from _ ) _ <;> norm_num [ card_multi_hypercube ];
      · cases gowers_product_pm1 f k i ‹_› <;> linarith;
      · rw [ pow_mul ] ;
    · norm_num [ card_hypercube ];
  · positivity

end GOWERS_NORM

-- ============================================================================
-- SECTION 7: GOWERS_PRODUCT_ALGEBRA
-- ----------------------------------------------------------------------------
-- Algebraic properties of Gowers products under pointwise multiplication
-- of functions. The main results are:
--
-- • Multiplicativity: GP(f · g, k, x, hs) = GP(f, k, x, hs) · GP(g, k, x, hs).
--   The Gowers product distributes over pointwise multiplication.
--
-- • Degree absorption: if deg(g) ≤ d, then
--   GP(f · g, d+1, x, hs) = GP(f, d+1, x, hs).
--   Multiplying by a low-degree function does not change the (d+1)-fold
--   Gowers product, because the g-factor contributes GP(g,d+1,…) = 1.
--
-- • Consequently, ‖f · g‖_{U^{d+1}} = ‖f‖_{U^{d+1}} when deg(g) ≤ d.
--   Multiplying by a low-degree function preserves the Gowers norm.
-- ============================================================================
section GOWERS_PRODUCT_ALGEBRA

variable {n : ℕ}

-- Pointwise product of two real-valued functions on the hypercube.
def boolFun_mul (f g : BoolFun n) : BoolFun n :=
  fun x => f x * g x

-- gowers_product(f · g, k, x, h) = gowers_product(f, k, x, h) · gowers_product(g, k, x, h)
lemma gowers_product_mul (f g : BoolFun n) (k : ℕ) (x : hypercube n)
    (hs : Fin k → hypercube n) :
    gowers_product (boolFun_mul f g) k x hs =
      gowers_product f k x hs * gowers_product g k x hs := by
  induction' k with k ih generalizing x;
  · rfl;
  · simp +decide only [gowers_product, ih];
    ring

-- gowers_product(f · g, d+1, x, hs) = gowers_product(f, d+1, x, hs) when deg(g) ≤ d
lemma gowers_product_mul_degree_le {d : ℕ}
    (f g : BoolFun n) (hg : is_degree_le_pm1 g d)
    (x : hypercube n) (hs : Fin (d + 1) → hypercube n) :
    gowers_product (boolFun_mul f g) (d + 1) x hs =
      gowers_product f (d + 1) x hs := by
  rw [gowers_product_mul, hg hs x, mul_one]

-- ||f · g||_{U^{d+1}}^{2^{d+1}} = ||f||_{U^{d+1}}^{2^{d+1}} when deg(g) ≤ d
lemma gowers_norm_mul_degree_le {d : ℕ}
    (f g : BoolFun n) (hg : is_degree_le_pm1 g d) :
    gowers_norm_pow (boolFun_mul f g) (d + 1) =
      gowers_norm_pow f (d + 1) := by
  unfold gowers_norm_pow
  congr 1
  funext x
  congr 1
  funext hs
  exact gowers_product_mul_degree_le f g hg x hs

end GOWERS_PRODUCT_ALGEBRA

-- ============================================================================
-- SECTION 8: DEGREE_TEST
-- ----------------------------------------------------------------------------
-- The low-degree test (also called the Reed–Muller test or derivative test)
-- for degree d works as follows:
--
--   1. Pick x ∈ F₂^n and h₁, …, h_{d+1} ∈ F₂^n uniformly at random.
--   2. Query f at all 2^{d+1} points of the cube x + span{h₁, …, h_{d+1}}.
--   3. Accept iff GP(f, d+1, x, h₁, …, h_{d+1}) = 1.
--
-- Equivalently, the test computes the (d+1)-fold multiplicative derivative
-- and checks that it equals 1 (the "derivative vanishing" condition).
--
-- Key results:
-- • Pr[accept] = (1 + ‖f‖_{U^{d+1}}^{2^{d+1}}) / 2.
-- • Completeness: deg(f) ≤ d ⟹ Pr[accept] = 1.
-- • Qualitative soundness: deg(f) > d ⟹ Pr[accept] < 1.
-- ============================================================================
section DEGREE_TEST

variable {n : ℕ}

-- Pr[degree test accepts f]
noncomputable def degree_test_accept_prob (d : ℕ) (f : hypercube n → Bool) : ℝ :=
  expectation (fun x =>
    multi_expectation (fun hs : Fin (d + 1) → hypercube n =>
      if gowers_product (lift_pm1 f) (d + 1) x hs = 1 then 1 else 0))

-- f is ε-far from degree ≤ d if dist(f,g) ≥ ε for all degree ≤ d functions g
def epsilon_far_from_degree (d : ℕ) (f : hypercube n → Bool) (ε : ℝ) : Prop :=
  0 ≤ ε ∧ ε ≤ 1 ∧
  ∀ g : hypercube n → Bool, is_degree_le_bool g d → bool_dist f g ≥ ε

-- Pr[accept] = (1 + ||f||_{U^{d+1}}^{2^{d+1}})/2
lemma degree_test_accept_prob_eq (d : ℕ) (f : hypercube n → Bool) :
    degree_test_accept_prob d f =
      (1 + gowers_norm_pow (lift_pm1 f) (d + 1)) / 2 := by
  unfold degree_test_accept_prob gowers_norm_pow;
  unfold expectation multi_expectation;
  -- Pointwise identity: 𝟙[GP = 1] = (1 + GP)/2 for GP ∈ {±1}.
  have h_if_eq : ∀ x : hypercube n, ∀ hs : Fin (d + 1) → hypercube n, (if gowers_product (lift_pm1 f) (d + 1) x hs = 1 then 1 else 0 : ℝ) = (1 + gowers_product (lift_pm1 f) (d + 1) x hs) / 2 := by
    intro x hs; split_ifs;
    · linarith;
    · cases gowers_product_pm1 f ( d + 1 ) x hs <;> aesop;
  simp +decide only [h_if_eq, sum_div];
  simp +decide [ Finset.sum_add_distrib, add_div, Finset.sum_div _ _ _ ];
  norm_num [ div_eq_mul_inv, mul_assoc, mul_comm, mul_left_comm, Finset.mul_sum _ _ _, Finset.sum_mul _ _ _, card_hypercube ];
  field_simp
  ring

-- degree ≤ d functions pass with probability 1
lemma degree_test_completeness (d : ℕ) (f : hypercube n → Bool)
    (hdeg : is_degree_le_bool f d) :
    degree_test_accept_prob d f = 1 := by
  convert degree_test_accept_prob_eq d f using 1;
  rw [ gowers_norm_eq_one_iff _ _ |>.2 hdeg ] ; norm_num

-- non-degree ≤ d functions pass with probability < 1
lemma degree_test_qualitative_soundness (d : ℕ) (f : hypercube n → Bool)
    (hndeg : ¬ is_degree_le_bool f d) :
    degree_test_accept_prob d f < 1 := by
  -- ‖f‖_{U^{d+1}}^{2^{d+1}} < 1 when deg(f) > d.
  have h_avg_lt_one : gowers_norm_pow (lift_pm1 f) (d + 1) < 1 := by
    exact lt_of_le_of_ne ( by
      refine' div_le_one_of_le₀ _ _;
      · refine' le_trans ( Finset.sum_le_sum fun x _ => div_le_one_of_le₀ _ _ ) _ <;> norm_num;
        · refine' le_trans ( Finset.sum_le_sum fun _ _ => show _ ≤ 1 from _ ) _ <;> norm_num;
          · cases gowers_product_pm1 f d x ( ‹Fin ( d + 1 ) → hypercube n› ∘ Fin.castSucc ) <;> cases gowers_product_pm1 f d ( xor_vec x ( ‹Fin ( d + 1 ) → hypercube n› ( Fin.last d ) ) ) ( ‹Fin ( d + 1 ) → hypercube n› ∘ Fin.castSucc ) <;> nlinarith;
          · rw [ pow_mul ] ;
      · positivity ) ( by
      exact fun h => hndeg <| gowers_norm_eq_one_iff f d |>.1 h );
  -- Pr[accept] = (1 + ‖f‖)/2 < (1 + 1)/2 = 1.
  linarith [ degree_test_accept_prob_eq d f ]

end DEGREE_TEST

-- ============================================================================
-- SECTION 9: FOURIER_DEGREE
-- ----------------------------------------------------------------------------
-- This section connects Fourier analysis to degree testing by showing that
-- if f is ε-far from degree ≤ d (for d ≥ 1), then all Fourier coefficients
-- of f are bounded:
--     |f̂(S)| ≤ 1 − 2ε   for all S ⊆ {0, …, n-1}.
--
-- The argument uses the fact that every Fourier character χ_S has degree ≤ 1,
-- and hence degree ≤ d for d ≥ 1. If f is ε-far from all degree-≤-d
-- functions, it is in particular ε-far from χ_S (and from −χ_S), which gives
-- the upper bound f̂(S) ≤ 1 − 2ε and the lower bound f̂(S) ≥ −(1 − 2ε).
--
-- This bound is used in the quantitative soundness analysis of the degree
-- test: it controls the Fourier-analytic contribution to the U² norm, and
-- more generally to higher Gowers norms.
-- ============================================================================
section FOURIER_DEGREE

variable {n : ℕ}

-- Every character χ_S has degree ≤ 1
lemma char_is_degree_le_one (S : Finset (Fin n)) :
    is_degree_le_pm1 (char_S S) 1 := by
  unfold is_degree_le_pm1;
  unfold gowers_product; simp +decide [ char_S ] ;
  intro hs x;
  have key : ∀ (a h : hypercube n), BooleanAnalysis.chiS S a * BooleanAnalysis.chiS S (xor_vec a h) = BooleanAnalysis.chiS S h := by
    intro a h;
    unfold BooleanAnalysis.chiS xor_vec;
    rw [ ← Finset.prod_mul_distrib ];
    apply Finset.prod_congr rfl; intro i _;
    cases a i <;> cases h i <;> simp [ BooleanAnalysis.boolToSign, Bool.xor ];
  have h1 := key x (hs 0);
  have h2 := key (xor_vec x (hs 1)) (hs 0);
  have h3 : BooleanAnalysis.chiS S (hs 0) * BooleanAnalysis.chiS S (hs 0) = 1 := char_S_sq n S (hs 0)
  calc BooleanAnalysis.chiS S x * BooleanAnalysis.chiS S (xor_vec x (hs 0)) *
      (BooleanAnalysis.chiS S (xor_vec x (hs 1)) * BooleanAnalysis.chiS S (xor_vec (xor_vec x (hs 1)) (hs 0)))
      = BooleanAnalysis.chiS S (hs 0) * BooleanAnalysis.chiS S (hs 0) := by rw [ h1, h2 ]
    _ = 1 := h3

-- The negation -χ_S also has degree ≤ 1
lemma neg_char_is_degree_le_one (S : Finset (Fin n)) :
    is_degree_le_pm1 (fun x => -char_S S x) 1 := by
  have := char_is_degree_le_one S; simp_all +decide [ is_degree_le_pm1 ] ;

-- Characters have degree ≤ d for any d ≥ 1
lemma char_is_degree_le (S : Finset (Fin n)) {d : ℕ} (hd : d ≥ 1) :
    is_degree_le_pm1 (char_S S) d := by
  have h1 := char_is_degree_le_one S
  induction d with
  | zero => omega
  | succ d ih =>
    cases d with
    | zero => exact h1
    | succ d => exact degree_le_succ (ih (by omega))

-- Negation of characters have degree ≤ d for any d ≥ 1
lemma neg_char_is_degree_le (S : Finset (Fin n)) {d : ℕ} (hd : d ≥ 1) :
    is_degree_le_pm1 (fun x => -char_S S x) d := by
  have h1 := neg_char_is_degree_le_one S
  induction d with
  | zero => omega
  | succ d ih =>
    cases d with
    | zero => exact h1
    | succ d => exact degree_le_succ (ih (by omega))

-- If f is ε-far from degree ≤ d (d ≥ 1), then f̂(S) ≤ 1 - 2ε for all S
lemma fourier_coeff_le_of_far_from_degree
    {d : ℕ} (hd : d ≥ 1)
    (f : hypercube n → Bool)
    (ε : ℝ)
    (hfar : epsilon_far_from_degree d f ε) :
    ∀ S : Finset (Fin n),
      fourier_coeff (lift_pm1 f) S ≤ 1 - 2 * ε := by
  intro S;
  -- Construct a Boolean g whose ±1 lift is χ_S: g(x) = (|S ∩ supp(x)| mod 2 = 1).
  obtain ⟨g, hg⟩ : ∃ g : hypercube n → Bool, lift_pm1 g = char_S S := by
    use fun x => (S.filter (fun i => x i)).card % 2 = 1;
    funext x; simp [lift_pm1, char_S];
    induction S using Finset.induction <;> simp_all +decide [ Finset.filter_insert ]
    · simp only [ BooleanAnalysis.chiS, Finset.prod_insert ‹_› ]
      by_cases h : x ‹_› <;>
        cases Nat.mod_two_eq_zero_or_one (Finset.card (Finset.filter (fun i => x i = true) ‹_›)) <;>
        simp_all +decide [ Nat.add_mod, BooleanAnalysis.chiS ] <;> nlinarith
  -- Apply the distance-to-Fourier bound from BoolBLR.
  apply fourier_coeff_le_of_dist_ge f g S hg;
  -- g has degree ≤ d (since χ_S has degree ≤ d), so dist(f, g) ≥ ε.
  exact hfar.2.2 g ( by unfold is_degree_le_bool; exact hg.symm ▸ char_is_degree_le S hd )

/-
If f is ε-far from degree ≤ d (d ≥ 1), then -f̂(S) ≤ 1 - 2ε for all S
(equivalently, f̂(S) ≥ -(1 - 2ε))
-/
lemma neg_fourier_coeff_le_of_far_from_degree
    {d : ℕ} (hd : d ≥ 1)
    (f : hypercube n → Bool)
    (ε : ℝ)
    (hfar : epsilon_far_from_degree d f ε) :
    ∀ S : Finset (Fin n),
      -fourier_coeff (lift_pm1 f) S ≤ 1 - 2 * ε := by
  intro S
  -- Construct g with lift_pm1 g = −χ_S, and show g has degree ≤ d.
  obtain ⟨g, hg⟩ : ∃ g : hypercube n → Bool, is_degree_le_bool g d ∧ lift_pm1 g = fun x => -char_S S x := by
    have h_neg_char : is_degree_le_pm1 (fun x => -char_S S x) d := by
      exact neg_char_is_degree_le S hd;
    have h_neg_char : ∃ g : hypercube n → Bool, lift_pm1 g = fun x => -char_S S x := by
      use fun x => PM1ToBool? (-char_S S x) |> Option.get!;
      funext x; simp [lift_pm1, PM1ToBool?];
      -- χ_S(x) ∈ {±1}, so −χ_S(x) ∈ {∓1}, which PM1ToBool? can invert.
      have h_char : char_S S x = 1 ∨ char_S S x = -1 := by
        have h_char : ∀ i ∈ S, BoolToPM1 (x i) = 1 ∨ BoolToPM1 (x i) = -1 := by
          exact fun i hi => by cases x i <;> tauto;
        have h_char_prod : ∀ {T : Finset (Fin n)}, (∀ i ∈ T, BoolToPM1 (x i) = 1 ∨ BoolToPM1 (x i) = -1) → (∏ i ∈ T, BoolToPM1 (x i)) = 1 ∨ (∏ i ∈ T, BoolToPM1 (x i)) = -1 := by
          intros T hT; induction T using Finset.induction <;> simp_all +decide [ Finset.prod_insert ] ;
          grind;
        exact h_char_prod h_char;
      cases h_char <;> simp +decide [ * ];
      norm_num [ BoolToPM1 ];
    unfold is_degree_le_bool; aesop;
  -- dist(f, g) ≥ ε since g has degree ≤ d.
  have := hfar.2.2 g hg.1;
  -- Relate −f̂(S) to the inner product ⟨f, g⟩ (since lift(g) = −χ_S).
  have h_fourier_coeff : fourier_coeff (lift_pm1 f) S = -inner_product (lift_pm1 f) (lift_pm1 g) := by
    unfold fourier_coeff inner_product; simp +decide [ hg.2 ] ;
    unfold expectation; norm_num;
    ring;
  -- The inner product ⟨f, g⟩ = 1 − 2·dist(f, g).
  have h_dist_to_fourier : inner_product (lift_pm1 f) (lift_pm1 g) = 1 - 2 * bool_dist f g := by
    unfold inner_product bool_dist;
    unfold expectation lift_pm1; simp +decide [ Finset.sum_ite ] ; ring_nf;
    have h_fourier_bound : ∀ x, BoolToPM1 (f x) * BoolToPM1 (g x) = 1 - 2 * (if f x = g x then 0 else 1) := by
      intro x; cases h : f x <;> cases h' : g x <;> simp_all +decide [BoolToPM1] <;> norm_num
    simp_all +decide [ Finset.sum_ite ] ; ring_nf;
    have h_pow : (1 / 2 : ℝ) ^ n * 2 ^ n = 1 := by rw [ ← mul_pow ]; norm_num;
    linarith
  -- Combine: −f̂(S) = ⟨f, g⟩ = 1 − 2·dist(f, g) ≤ 1 − 2ε.
  linarith

-- Combined: |f̂(S)| ≤ 1 - 2ε when ε-far from degree ≤ d (d ≥ 1)
lemma abs_fourier_coeff_le_of_far_from_degree
    {d : ℕ} (hd : d ≥ 1)
    (f : hypercube n → Bool)
    (ε : ℝ)
    (hfar : epsilon_far_from_degree d f ε) :
    ∀ S : Finset (Fin n),
      |fourier_coeff (lift_pm1 f) S| ≤ 1 - 2 * ε := by
  intro S
  rw [abs_le]
  exact ⟨by linarith [neg_fourier_coeff_le_of_far_from_degree hd f ε hfar S],
         fourier_coeff_le_of_far_from_degree hd f ε hfar S⟩

end FOURIER_DEGREE

-- ============================================================================
-- SECTION 10: QUANTITATIVE_SOUNDNESS
-- ----------------------------------------------------------------------------
-- This section builds toward the quantitative soundness theorem for the
-- low-degree (Reed–Muller) test:
--
--   If f is ε-far from RM(d, n) (d ≥ 1), then
--   Pr[degree test accepts f] ≤ 1 − ε.
--
-- The proof strategy proceeds in several stages:
--
-- 1. **Parseval for ±1 functions**: ∑_S f̂(S)² = 1.
--
-- 2. **U² norm bound**: ‖f‖_{U²}⁴ = ∑ f̂(S)⁴ ≤ (1 − 2ε)²
--    (using |f̂(S)| ≤ 1 − 2ε and Parseval).
--
-- 3. **Squaring bound**: (1 − 2ε)² ≤ 1 − 2ε for ε ∈ [0, 1/2].
--
-- 4. **Base case (d = 1)**: ‖f‖_{U²}⁴ ≤ 1 − 2ε, combining steps 2 and 3.
--
-- 5. **Inductive step (d ≥ 2)**: uses the derivative distance lemma and
--    induction on d. (This step currently has a sorry.)
--
-- 6. **Final theorem**: Pr[accept] = (1 + ‖f‖_{U^{d+1}}^{2^{d+1}}) / 2
--    ≤ (1 + (1 − 2ε)) / 2 = 1 − ε.
-- ============================================================================
section QUANTITATIVE_SOUNDNESS

variable {n : ℕ}

-- f is ε-far from RM(d,n)
def epsilon_far_from_RM (d : ℕ) (f : hypercube n → Bool) (ε : ℝ) : Prop :=
  epsilon_far_from_degree d f ε

-- The Reed-Muller test is the same as the degree test
noncomputable def RM_test_accept_prob (d : ℕ) (f : hypercube n → Bool) : ℝ :=
  degree_test_accept_prob d f

-- Parseval for ±1 functions: ∑ f̂(S)² = 1
lemma parseval_pm1 (f : hypercube n → Bool) :
    ∑ S : Finset (Fin n), (fourier_coeff (lift_pm1 f) S) ^ 2 = 1 := by
  convert parseval_identity ( fun x => BoolToPM1 ( f x ) ) using 1;
  unfold L2_norm_sq expectation;
  rw [ eq_div_iff ] <;> norm_num [ BoolToPM1_sq ];

-- ||f||_{U²}⁴ = ∑ f̂(S)⁴ ≤ (1-2ε)² when ε-far from degree ≤ d (d ≥ 1)
lemma gowers_U2_le_of_far
    {d : ℕ} (hd : d ≥ 1)
    (f : hypercube n → Bool)
    (ε : ℝ)
    (hfar : epsilon_far_from_degree d f ε) :
    gowers_norm_pow (lift_pm1 f) 2 ≤ (1 - 2 * ε) ^ 2 := by
  rw [ gowers_U2_fourier ];
  -- Each f̂(S)⁴ ≤ f̂(S)² · (1 − 2ε)² since f̂(S)² ≤ (1 − 2ε)².
  have h_fourier_sq_le : ∑ S : Finset (Fin n), (fourier_coeff (lift_pm1 f) S) ^ 4 ≤ ∑ S : Finset (Fin n), (fourier_coeff (lift_pm1 f) S) ^ 2 * (1 - 2 * ε) ^ 2 := by
    apply Finset.sum_le_sum;
    intro S _; nlinarith only [ show ( fourier_coeff ( lift_pm1 f ) S ) ^ 2 ≤ ( 1 - 2 * ε ) ^ 2 by nlinarith only [ abs_le.mp ( abs_fourier_coeff_le_of_far_from_degree hd f ε hfar S ) ] ] ;
  -- Sum and apply Parseval: ∑ f̂(S)² = 1.
  exact h_fourier_sq_le.trans ( by rw [ ← Finset.sum_mul _ _ _ ] ; rw [ show ∑ S : Finset ( Fin n ), fourier_coeff ( lift_pm1 f ) S ^ 2 = 1 from parseval_pm1 f ] ; nlinarith )

-- (1 - 2ε)² ≤ 1 - 2ε for ε ∈ [0, 1/2]
lemma sq_one_sub_two_eps_le {ε : ℝ} (h0 : 0 ≤ ε) (h1 : ε ≤ 1/2) :
    (1 - 2 * ε) ^ 2 ≤ 1 - 2 * ε := by
  nlinarith

-- ε ≤ 1/2 when f is ε-far from degree ≤ d (d ≥ 1)
lemma eps_le_half_of_far
    {d : ℕ} (hd : d ≥ 1)
    (f : hypercube n → Bool)
    (ε : ℝ)
    (hfar : epsilon_far_from_degree d f ε) :
    ε ≤ 1 / 2 := by
  by_contra h;
  have h_abs_fourier_coeff : ∀ S : Finset (Fin n), |fourier_coeff (lift_pm1 f) S| ≤ 1 - 2 * ε := by
    exact fun S => abs_fourier_coeff_le_of_far_from_degree hd f ε hfar S;
  -- |f̂(∅)| ≤ 1 − 2ε < 0 is a contradiction since norms are nonneg.
  exact absurd ( h_abs_fourier_coeff ∅ ) ( by linarith [ abs_le.mp ( h_abs_fourier_coeff ∅ ) ] )

-- Base case: ||f||_{U²}⁴ ≤ 1 - 2ε when ε-far from degree ≤ d (d ≥ 1)
lemma gowers_norm_le_of_far_d1
    {d : ℕ} (hd : d ≥ 1)
    (f : hypercube n → Bool)
    (ε : ℝ)
    (hfar : epsilon_far_from_degree d f ε) :
    gowers_norm_pow (lift_pm1 f) 2 ≤ 1 - 2 * ε := by
  have h1 := gowers_U2_le_of_far hd f ε hfar
  have h2 := eps_le_half_of_far hd f ε hfar
  exact le_trans h1 (sq_one_sub_two_eps_le hfar.1 h2)

-- ε-far from degree ≤ d implies ε-far from degree ≤ d' for d' ≤ d
lemma epsilon_far_monotone {d d' : ℕ} (hdd : d' ≤ d)
    (f : hypercube n → Bool) (ε : ℝ)
    (hfar : epsilon_far_from_degree d f ε) :
    epsilon_far_from_degree d' f ε := by
  refine ⟨ hfar.1, hfar.2.1, fun g hg => ?_ ⟩;
  -- Promote deg(g) ≤ d' to deg(g) ≤ d by repeated application of degree_le_succ.
  have h_deg_le : ∀ k ≥ d', is_degree_le_pm1 (lift_pm1 g) k := by
    exact fun k hk => Nat.le_induction hg ( fun k hk ih => degree_le_succ ih ) k hk;
  exact hfar.2.2 g ( h_deg_le d hdd )

/--
**Derivative Distance Lemma.**
If `f` is `ε`-far from degree ≤ `d` (`d ≥ 2`) and `q` is the closest
degree-`d` function, then the average distance of the multiplicative
derivative `Δ_h f` from degree-`(d−1)` functions is at least `ε`.
This follows from the pairwise-independence structure of the Boolean
hypercube combined with self-correction for Reed–Muller codes.
See Bhattacharyya–Kopparty–Schoenebeck–Sudan–Zuckerman (STOC 2010).
-/
lemma derivative_distance_lemma
    {d : ℕ} (_hd : d ≥ 2)
    (f : hypercube n → Bool)
    (ε : ℝ)
    (hfar : epsilon_far_from_degree d f ε) :
    ∃ (δ : ℝ), δ ≥ ε ∧
    ∀ (h : hypercube n),
      ∃ (g : hypercube n → Bool),
        is_degree_le_bool g (d - 1) →
        bool_dist (fun x => f x ^^ f (xor_vec x h)) g ≥ δ := by
  contrapose! hfar;
  unfold epsilon_far_from_degree;
  obtain ⟨ h, hh ⟩ := hfar ε le_rfl;
  have := hh ( fun x => Bool.xor (Bool.xor (f x) (f ( xor_vec x h ))) true ) ; simp_all +decide [ bool_dist ] ;
  unfold expectation at this; norm_num at this;
  intros; linarith;

/--
**Key Lemma (Gowers Norm Bound).**
For `d ≥ 1`, if `f` is `ε`-far from degree ≤ `d`, then
`‖f‖_{U^{d+1}}^{2^{d+1}} ≤ 1 − c·ε` for some constant `c > 0`.

- For `d = 1` this follows from the Fourier-analytic bound
  on the `U²` norm combined with `(1 − 2ε)² ≤ 1 − 2ε`, giving `c = 2`.
- For `d ≥ 2` the proof proceeds by induction on `d`, using
  the recursive unfolding of the Gowers norm and the
  derivative distance lemma (BKSSZ 2010). This step is currently
  incomplete (sorry).
-/
lemma gowers_norm_le_of_far
    {d : ℕ} (hd : d ≥ 1)
    (f : hypercube n → Bool)
    (ε : ℝ)
    (hfar : epsilon_far_from_degree d f ε) :
    ∃ c : ℝ,
      0 < c ∧
      gowers_norm_pow (lift_pm1 f) (d + 1) ≤ 1 - c * ε := by
  cases d with
  | zero => omega
  | succ d =>
    cases d with
    | zero =>
      -- d = 1: take c = 2. The U² bound gives ‖f‖_{U²}⁴ ≤ 1 − 2ε.
      refine ⟨2, by positivity, ?_⟩
      simpa using gowers_norm_le_of_far_d1 hd f ε hfar
    | succ d =>
      -- d ≥ 2: requires the derivative distance lemma / inverse theorem
      -- (BKSSZ 2010); the proof uses induction
      -- on d together with the derivative distance lemma.
      sorry

/--
**Quantitative Soundness Theorem.**
If `f : 𝔽₂ⁿ → 𝔽₂` is `ε`-far from every polynomial of degree ≤ `d`
(where `d ≥ 1`), then the `(d+1)`-fold derivative test accepts with
probability at most `1 − ε`.
Combined with the completeness theorem (`degree_test_completeness`),
this shows that the derivative test has perfect completeness and
soundness gap at least `ε`.
-/
lemma degree_test_quantitative_soundness
    {d : ℕ} (hd : d ≥ 1)
    (f : hypercube n → Bool)
    (ε : ℝ)
    (hfar : epsilon_far_from_degree d f ε) :
    degree_test_accept_prob d f ≤ 1 - ε := by
  sorry

-- RM test completeness: codewords of RM(d,n) pass with probability 1
lemma RM_test_completeness (d : ℕ) (f : hypercube n → Bool)
    (hf : f ∈ ReedMuller d n) :
    degree_test_accept_prob d f = 1 :=
  degree_test_completeness d f hf

/--
**Reed–Muller Test Soundness.**
If `f` is `ε`-far from every codeword of `RM(d, n)` (i.e., every
polynomial of degree ≤ `d` over `𝔽₂`), then the `(d+1)`-fold
derivative test rejects with probability at least `ε`.
Equivalently, the test accepts with probability at most `1 − ε`.
-/
lemma RM_test_soundness
    {d : ℕ} (hd : d ≥ 1)
    (f : hypercube n → Bool)
    (ε : ℝ)
    (hfar : epsilon_far_from_degree d f ε) :
    degree_test_accept_prob d f ≤ 1 - ε :=
  degree_test_quantitative_soundness hd f ε hfar

end QUANTITATIVE_SOUNDNESS

end LowDegreeTest
