/-
Copyright (c) 2026 Prastik Mohanraj. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prastik Mohanraj
-/

import Mathlib
open Finset Complex

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

namespace ZkFourier

set_option linter.unusedSectionVars false

/-!
# ZkFourier

## Main results

- `card_ZkVec`: The cardinality of (ZMod k)^n equals k^n.
- `isPrimitiveRoot_rootOfUnity`: The k-th root of unity exp(2πi/k) is a primitive k-th root of unity.
- `toOmega_add`: The embedding ω_k^(a+b) = ω_k^a · ω_k^b is a group homomorphism.
- `toOmega_neg`: Complex conjugation satisfies ω_k^(-a) = conj(ω_k^a).
- `geom_sum_toOmega`: Orthogonality of characters: ∑_{a} ω_k^{ja} = k if j=0, else 0.
- `char_s_mul`: Product rule for characters: χ_s(x) · χ_t(x) = χ_{s+t}(x).
- `inner_product_char_self`: Characters are unit-norm: ⟨χ_s, χ_s⟩ = 1.
- `inner_product_char_nonself`: Characters are orthogonal: ⟨χ_s, χ_t⟩ = 0 for s ≠ t.
- `fourier_expansion`: Every function expands as f(x) = ∑_s f̂(s) χ_s(x).
- `parseval_identity`: Parseval's identity: ∑_s |f̂(s)|² = ‖f‖₂².
- `fourier_coeff_convolution`: Convolution theorem: (f*g)^(s) = f̂(s) · ĝ(s).

## References

- Original formalization by Prastik Mohanraj
-/

-- ============================================================================
-- SECTION 1: DOMAIN
-- ----------------------------------------------------------------------------
-- This section defines the domain ℤ_k^n = (ZMod k)^n for Fourier analysis
-- over finite abelian groups. The vector space ℤ_k^n is the natural
-- generalization of the Boolean hypercube {0,1}^n ≅ F_2^n: each coordinate
-- takes values in the cyclic group ℤ/kℤ rather than ℤ/2ℤ. This domain
-- arises naturally in algebraic property testing (e.g., linearity testing
-- over ℤ_k) and in coding theory (Reed–Solomon and related codes).
--
-- We model ℤ_k^n as the function type Fin n → ZMod k and establish the
-- basic algebraic and finiteness instances needed for the rest of the theory:
-- decidable equality (for conditional expressions), Fintype (for finite sums
-- and expectations), the additive group structure (pointwise addition mod k),
-- and the module structure over ZMod k (for scalar multiplication).
-- ============================================================================
section DOMAIN

-- The n-dimensional vector space over ℤ/kℤ.
def ZkVec (k n : ℕ) := Fin n → ZMod k

-- Decidable equality on ZkVec — needed for `if x = y then … else …`
-- expressions and for use as keys in finite maps/sums.
instance {k n : ℕ} : DecidableEq (ZkVec k n) := by
  unfold ZkVec; infer_instance

-- ZkVec is a finite type (provided k ≥ 1, ensured by [NeZero k]),
-- since both Fin n and ZMod k are finite. This instance is required
-- for defining expectations (sums over all k^n elements).
instance {k n : ℕ} [NeZero k] : Fintype (ZkVec k n) := by
  unfold ZkVec; infer_instance

-- (x + y)(i) = x(i) + y(i) in ZMod k.
-- This makes ℤ_k^n into the direct product (ℤ/kℤ)^n as an abelian group.
instance {k n : ℕ} : AddCommGroup (ZkVec k n) := Pi.addCommGroup

-- The ZMod k-module structure on ℤ_k^n, giving scalar multiplication
-- (c • x)(i) = c · x(i). This allows us to write expressions like s · x
-- for the dot product and to use linear algebra over ℤ_k.
instance {k n : ℕ} : Module (ZMod k) (ZkVec k n) := Pi.module _ _ _

-- |Z_k^n| = k^n
lemma card_ZkVec (k : ℕ) [NeZero k] (n : ℕ) :
    Fintype.card (ZkVec k n) = k ^ n := by
  unfold ZkVec
  simp [Fintype.card_pi, ZMod.card]

end DOMAIN

-- ============================================================================
-- SECTION 2: EMBEDDING
-- ----------------------------------------------------------------------------
-- This section constructs the embedding of ℤ/kℤ into the complex unit circle
-- via the primitive k-th root of unity ω_k = exp(2πi/k). The map
--     a ↦ ω_k^a
-- is the fundamental group homomorphism (ℤ/kℤ, +) → (ℂ×, ·) that underlies
-- the entire Fourier theory on ℤ_k^n. It sends addition in ℤ_k to
-- multiplication on the unit circle, negation to complex conjugation,
-- and satisfies the crucial orthogonality relation
--     ∑_{a ∈ ℤ_k} ω_k^{ja} = k · 𝟙[j = 0].
--
-- This is the direct generalization of the Boolean embedding
--     Bool → ℝ:  false ↦ +1,  true ↦ -1
-- used in BoolFourier.lean: when k = 2, we have ω_2 = exp(πi) = -1, so
-- ω_2^0 = 1 and ω_2^1 = -1, recovering the ±1 embedding.
-- ============================================================================
section EMBEDDING

-- ω_k = exp(2π i / k)
noncomputable def rootOfUnity (k : ℕ) : ℂ :=
  Complex.exp (2 * ↑Real.pi * I / (k : ℂ))

-- a ↦ ω_k^a (lift from additive Z_k to multiplicative group on S^1)
noncomputable def toOmega {k : ℕ} [NeZero k] (a : ZMod k) : ℂ :=
  rootOfUnity k ^ a.val

-- ω_k is a primitive k-th root of unity
lemma isPrimitiveRoot_rootOfUnity {k : ℕ} [NeZero k] :
    IsPrimitiveRoot (rootOfUnity k) k :=
  Complex.isPrimitiveRoot_exp k (NeZero.ne k)

-- ω_k^k = 1
lemma rootOfUnity_pow_k {k : ℕ} [NeZero k] :
    rootOfUnity k ^ k = 1 :=
  isPrimitiveRoot_rootOfUnity.pow_eq_one

-- ω_k^0 = 1
@[simp]
lemma toOmega_zero {k : ℕ} [NeZero k] : toOmega (0 : ZMod k) = 1 := by
  simp [toOmega, ZMod.val_zero]

-- ω_k^(a+b) = ω_k^a · ω_k^b
lemma toOmega_add {k : ℕ} [NeZero k] (a b : ZMod k) :
    toOmega (a + b) = toOmega a * toOmega b := by
      unfold toOmega; simp +decide [ ← pow_add ] ;
      rw [ ← Nat.mod_add_div ( a.val + b.val ) k, pow_add, pow_mul ] ; norm_num [ rootOfUnity_pow_k ];
      rw [ ZMod.val_add ]

-- ω_k^(-a) = conjugate(ω_k^a)
private lemma toOmega_neg_aux_h_neg {k : Nat} [inst : NeZero k] (a : ZMod k) (ha : ¬a = 0) : (-a).val = k - a.val := by
  convert ZMod.neg_val' a using 1;
  rw [ Nat.mod_eq_of_lt ( Nat.sub_lt ( NeZero.pos k ) ( Nat.pos_of_ne_zero ( by simpa [ ZMod.val_eq_zero ] using ha ) ) ) ];

lemma toOmega_neg {k : ℕ} [NeZero k] (a : ZMod k) :
    toOmega (-a) = starRingEnd ℂ (toOmega a) := by
      by_cases ha : a.val = 0 <;> simp_all +decide;
      unfold toOmega rootOfUnity;
      rw [ (toOmega_neg_aux_h_neg a ha), ← Complex.exp_nat_mul, ← Complex.exp_nat_mul ];
      rw [ Nat.cast_sub ( show a.val ≤ k from a.val_lt.le ) ] ; simp +decide [ Complex.ext_iff, Complex.exp_re, Complex.exp_im];
      norm_num [ sub_mul, mul_div_cancel₀, NeZero.ne ];
      erw [ ZMod.cast_eq_val ] ; norm_cast ; aesop

-- |ω_k^a| = 1
lemma norm_toOmega {k : ℕ} [NeZero k] (a : ZMod k) :
    ‖toOmega a‖ = 1 := by
      unfold toOmega;
      unfold rootOfUnity; norm_num [ Complex.norm_exp ] ;

-- ω_k^(ja) = (ω_k^j)^a
lemma toOmega_mul {k : ℕ} [NeZero k] (j a : ZMod k) :
    toOmega (j * a) = (rootOfUnity k ^ j.val) ^ a.val := by
      unfold toOmega;
      rw [ ← pow_mul, ZMod.val_mul ];
      rw [ ← Nat.mod_add_div ( j.val * a.val ) k, pow_add, pow_mul ] ; norm_num [ rootOfUnity_pow_k ]

-- The orthogonality of characters on ℤ_k:
--     ∑_{a ∈ ℤ_k} ω_k^{ja} = k   if j = 0
--                              = 0   if j ≠ 0.
-- This is the fundamental identity of discrete Fourier analysis. When j ≠ 0,
-- the sum is a geometric series with ratio ω_k^j ≠ 1, so it telescopes to 0.
-- When j = 0, every term is 1 and the sum equals k.
private lemma geom_sum_toOmega_aux_h_j_val_ne_zero {k : Nat} [inst : NeZero k] (j : ZMod k) (h : ¬j = 0) : j.val ≠ 0 := by
  cases k <;> aesop;

private lemma geom_sum_toOmega_aux_h_nontrivial {k : Nat} [inst : NeZero k] (j : ZMod k) (h : ¬j = 0) : ∑ a ∈ Finset.range k, (rootOfUnity k ^ j.val) ^ a = 0 := by
  rw [ geom_sum_eq ] <;> norm_num;
  · exact Or.inl ( by rw [ ← pow_mul, Nat.mul_comm, pow_mul, rootOfUnity_pow_k, one_pow, sub_self ] );
  ·
    let h_j_val_ne_zero : j.val ≠ 0 := (geom_sum_toOmega_aux_h_j_val_ne_zero j h)
    exact fun h => h_j_val_ne_zero <| Nat.eq_zero_of_dvd_of_lt ( isPrimitiveRoot_rootOfUnity.pow_eq_one_iff_dvd _ |>.1 h ) ( ZMod.val_lt j );

lemma geom_sum_toOmega {k : ℕ} [NeZero k] (j : ZMod k) :
    ∑ a : ZMod k, toOmega (j * a) = if j = 0 then (k : ℂ) else 0 := by
      split_ifs with h;
      · simp [h];
      · -- When j ≠ 0, the sum is a geometric series with ratio ω_k^j ≠ 1.
        -- We evaluate it using the identity ∑_{a=0}^{k-1} r^a = (r^k - 1)/(r - 1) = 0,
        -- since r^k = ω_k^{jk} = (ω_k^k)^j = 1^j = 1.
        -- Reindex the sum from Finset.range k to ZMod k via the bijection a ↦ a.val.
        convert (geom_sum_toOmega_aux_h_nontrivial j h) using 1;
        refine' Finset.sum_bij ( fun a _ => a.val ) _ _ _ _ <;> simp +decide [ toOmega_mul ];
        · exact fun a => ZMod.val_lt a;
        · exact fun a₁ a₂ h => by simpa [ ZMod.natCast_zmod_val ] using congr_arg ( fun x : ℕ => x : ℕ → ZMod k ) h;
        · exact fun b hb => ⟨ b, ZMod.val_cast_of_lt hb ⟩

end EMBEDDING

-- ============================================================================
-- SECTION 3: FUNCTIONS
-- ----------------------------------------------------------------------------
-- This section defines the basic function space and analytic operations for
-- Fourier analysis on ℤ_k^n. A "ℤ_k-function" is a map ℤ_k^n → ℂ, and we
-- equip this space with:
--   • Expectation: E[f] = (1/k^n) ∑_x f(x), the uniform average over ℤ_k^n.
--   • Hermitian inner product: ⟨f,g⟩ = E[f · ḡ], using complex conjugation
--     because our characters take values in ℂ (not just ℝ as in the Boolean case).
--   • Squared L² norm: ‖f‖₂² = (1/k^n) ∑_x |f(x)|², a real-valued quantity.
--   • Convolution: (f * g)(x) = E_y[f(y) g(x-y)].
--
-- These are the direct analogues of the corresponding operations in
-- BoolFourier.lean, generalized from {0,1}^n/ℝ to ℤ_k^n/ℂ. The key
-- difference from the Boolean case is the use of complex conjugation in the
-- inner product, which is necessary because the characters ω_k^{s·x} are
-- complex-valued (not real-valued) when k ≥ 3.
-- ============================================================================
section FUNCTIONS

-- A ℤ_k-function: a complex-valued function on the domain ℤ_k^n.
-- These are the objects whose Fourier transforms we study.
def ZkFun (k n : ℕ) := ZkVec k n → ℂ

variable {k : ℕ} [NeZero k] {n : ℕ}

-- E[f] = (∑_x f(x)) / k^n
noncomputable def expectation (f : ZkFun k n) : ℂ :=
  (∑ x : ZkVec k n, f x) / (k : ℂ) ^ n

-- ⟨f,g⟩ = E[f(x) · conjugate(g(x))]
noncomputable def inner_product (f g : ZkFun k n) : ℂ :=
  expectation (fun x => f x * starRingEnd ℂ (g x))

-- ∥f∥_2^2 = E[|f(x)|^2]
noncomputable def L2_norm_sq (f : ZkFun k n) : ℝ :=
  (∑ x : ZkVec k n, ‖f x‖ ^ 2) / (k : ℝ) ^ n

-- (f * g)(x) = E[f(y) g(x-y)]
noncomputable def convolution (f g : ZkFun k n) : ZkFun k n :=
  fun x => expectation (fun y => f y * g (x - y))

end FUNCTIONS

-- ============================================================================
-- SECTION 4: CHARACTERS
-- ----------------------------------------------------------------------------
-- The Fourier characters of ℤ_k^n are the functions
--     χ_s(x) = ω_k^{s · x} = ω_k^{∑_i s_i x_i}
-- indexed by "frequency vectors" s ∈ ℤ_k^n. There are k^n characters,
-- matching the dimension of the function space, and they form an orthonormal
-- basis under the Hermitian inner product ⟨·,·⟩:
--     ⟨χ_s, χ_t⟩ = 1 if s = t, and 0 otherwise.
--
-- This generalizes the Boolean Fourier characters χ_S(x) = ∏_{i∈S}(-1)^{x_i}
-- from BoolFourier.lean: when k = 2, the "dot product" s · x reduces to
-- the parity ∑ s_i x_i mod 2, and ω_2^{parity} = (-1)^{parity}.
--
-- Key properties established here:
--   • Multiplicativity: χ_s(x+y) = χ_s(x) · χ_s(y).
--   • Product rule: χ_s(x) · χ_t(x) = χ_{s+t}(x).
--   • Conjugate: conj(χ_s(x)) = χ_{-s}(x).
--   • Unit norm: |χ_s(x)| = 1.
--   • Orthogonality: E[χ_s] = 0 for s ≠ 0, and E[χ_0] = 1.
-- ============================================================================
section CHARACTERS

variable {k : ℕ} [NeZero k] {n : ℕ}

-- s · x = ∑_i s_i x_i
def zkDot (s x : ZkVec k n) : ZMod k := ∑ i : Fin n, s i * x i

-- χ_s(x) = ω_k^{s·x}
noncomputable def char_s (s : ZkVec k n) : ZkFun k n :=
  fun x => toOmega (zkDot s x)

-- s·(x+y) = s·x + s·y
lemma zkDot_add_right (s x y : ZkVec k n) :
    zkDot s (x + y) = zkDot s x + zkDot s y := by
      unfold zkDot;
      simpa only [ ← Finset.sum_add_distrib ] using Finset.sum_congr rfl fun _ _ => mul_add _ _ _

-- 0·x = 0
lemma zkDot_zero_left (x : ZkVec k n) : zkDot 0 x = 0 := by
  exact Finset.sum_eq_zero fun i _ => MulZeroClass.zero_mul _

-- s·0 = 0
lemma zkDot_zero_right (s : ZkVec k n) : zkDot s 0 = 0 := by
  exact Finset.sum_eq_zero fun _ _ => mul_zero _

-- (-s)·x = -(s·x)
lemma zkDot_neg_left (s x : ZkVec k n) :
    zkDot (-s) x = -(zkDot s x) := by
      unfold zkDot; simp +decide [ ← Finset.sum_neg_distrib ] ;
      exact Finset.sum_congr rfl fun _ _ => neg_mul _ _

-- (s-t)·x = s·x - t·x
private lemma zkDot_sub_aux_h_expand {k : Nat} [inst : NeZero k] {n : Nat} (s t x : ZkVec k n) (i : Fin n) : (s - t) i * x i = s i * x i - t i * x i := by
  exact by rw [ Pi.sub_apply, sub_mul ];

lemma zkDot_sub (s t x : ZkVec k n) :
    zkDot (s - t) x = zkDot s x - zkDot t x := by
      let h_expand : ∀ i : Fin n, (s - t) i * x i = s i * x i - t i * x i := (zkDot_sub_aux_h_expand s t x)
      unfold zkDot; aesop;

-- χ_s(x+y) = χ_s(x) χ_s(y)
lemma char_s_add (s : ZkVec k n) (x y : ZkVec k n) :
    char_s s (x + y) = char_s s x * char_s s y := by
  simp only [char_s, zkDot_add_right, toOmega_add]

-- χ_s(0) = 1
@[simp]
lemma char_s_zero_vec (s : ZkVec k n) : char_s s 0 = 1 := by
  simp only [char_s, zkDot_zero_right, toOmega_zero]

-- χ_0(x) = 1
@[simp]
lemma char_s_zero_index (x : ZkVec k n) :
    char_s (0 : ZkVec k n) x = 1 := by
  simp only [char_s, zkDot_zero_left, toOmega_zero]

-- |χ_s(x)| = 1
lemma norm_char_s (s : ZkVec k n) (x : ZkVec k n) :
    ‖char_s s x‖ = 1 := norm_toOmega _

-- χ_s(x) ≠ 0
private lemma char_s_ne_zero_aux_h_anon_1 {k : Nat} [inst : NeZero k] {n : Nat} (s x : ZkVec k n) (h : char_s s x = 0) : ‖char_s s x‖ = 1 :=
  norm_char_s s x

lemma char_s_ne_zero (s : ZkVec k n) (x : ZkVec k n) :
    char_s s x ≠ 0 := by
  intro h
  let h_anon_1 : ‖char_s s x‖ = 1 := (char_s_ne_zero_aux_h_anon_1 s x h)
  rw [h, norm_zero] at h_anon_1; exact one_ne_zero h_anon_1.symm

-- conjugate(χ_s(x)) = χ_{-s}(x)
lemma char_s_conj (s : ZkVec k n) (x : ZkVec k n) :
    starRingEnd ℂ (char_s s x) = char_s (-s) x := by
  simp only [char_s, zkDot_neg_left, ← toOmega_neg]

-- χ_s(x) χ_t(x) = χ_{s+t}(x)
private lemma char_s_mul_aux_h_dot {k : Nat} [inst : NeZero k] {n : Nat} (s t x : ZkVec k n) : zkDot (s + t) x = ∑ i, (s i + t i) * x i := by
  rfl;

lemma char_s_mul (s t : ZkVec k n) (x : ZkVec k n) :
    char_s s x * char_s t x = char_s (s + t) x := by
      convert toOmega_add ( zkDot s x ) ( zkDot t x ) using 1;
      · convert toOmega_add ( zkDot s x ) ( zkDot t x ) |> Eq.symm using 1;
      · convert toOmega_add ( zkDot s x ) ( zkDot t x ) using 1;
        convert congr_arg ( fun z => toOmega z ) (char_s_mul_aux_h_dot s t x) using 1;
        simp +decide [ add_mul, Finset.sum_add_distrib, zkDot ]

-- E[χ_s] = 0 for s ≠ 0
private lemma expectation_char_nontrivial_aux_h_fubini {k : Nat} [inst : NeZero k] {n : Nat} {s : ZkVec k n} (hs : s ≠ 0) : ∑ x : ZkVec k n, toOmega (zkDot s x) = ∏ i : Fin n, ∑ x_i : ZMod k, toOmega (s i * x_i) := by
  rw [ Finset.prod_sum ];
  refine' Finset.sum_bij ( fun a _ => fun i _ => a i ) _ _ _ _ <;> simp +decide [ zkDot ];
  · simp +decide [ funext_iff ];
    exact fun a₁ a₂ h => funext h;
  · exact fun b => ⟨ fun i => b i ( Finset.mem_univ i ), rfl ⟩;
  · intro a; induction' ( Finset.univ : Finset ( Fin n ) ) using Finset.induction <;> simp_all +decide [ Finset.prod_insert, Finset.sum_insert ] ;
    rw [ ← ‹toOmega ( ∑ i ∈ _, s i * a i ) = ∏ i ∈ _, toOmega ( s i * a i ) ›, toOmega_add ];

lemma expectation_char_nontrivial {s : ZkVec k n} (hs : s ≠ 0) :
    expectation (char_s s) = 0 := by
      -- Factor the sum over ℤ_k^n as a product of one-dimensional sums.
      let h_fubini : ∑ x : ZkVec k n, toOmega (zkDot s x) = ∏ i : Fin n, ∑ x_i : ZMod k, toOmega (s i * x_i) := (expectation_char_nontrivial_aux_h_fubini hs)
      -- Since s ≠ 0, there exists some coordinate i where s_i ≠ 0.
      obtain ⟨i, hi⟩ : ∃ i : Fin n, s i ≠ 0 := by
        exact Function.ne_iff.mp hs;
      -- The i-th factor in the product is ∑_{x_i} ω_k^{s_i x_i} = 0
      -- by the geometric sum identity (since s_i ≠ 0).
      -- A product containing a zero factor is zero.
      unfold expectation char_s; simp_all +decide [h_fubini];
      exact Or.inl <| Finset.prod_eq_zero ( Finset.mem_univ i ) <| by simpa [ hi ] using geom_sum_toOmega ( s i ) ;

-- E[χ_0] = 1
lemma expectation_char_trivial :
    expectation (char_s (0 : ZkVec k n)) = 1 := by
      unfold expectation;
      rw [ div_eq_iff ] <;> norm_cast <;> norm_num [ card_ZkVec ];
      aesop

-- ⟨χ_s, χ_s⟩ = 1
lemma inner_product_char_self (s : ZkVec k n) :
    inner_product (char_s s) (char_s s) = 1 := by
      unfold inner_product;
      simp_all +decide [ Complex.mul_conj, Complex.normSq_eq_norm_sq, norm_char_s ];
      unfold expectation;
      norm_num [ card_ZkVec ]

-- ⟨χ_s, χ_t⟩ = 0 for s ≠ t
lemma inner_product_char_nonself {s t : ZkVec k n} (hst : s ≠ t) :
    inner_product (char_s s) (char_s t) = 0 := by
      simp [inner_product, char_s_mul, char_s_conj];
      exact expectation_char_nontrivial ( by contrapose! hst; simpa using eq_neg_of_add_eq_zero_left hst )

end CHARACTERS

-- ============================================================================
-- SECTION 5: FOURIER_COEFFICIENTS
-- ----------------------------------------------------------------------------
-- The Fourier coefficients of a function f : ℤ_k^n → ℂ are defined as
--     f̂(s) = ⟨f, χ_s⟩ = E_x[f(x) · conj(χ_s(x))]
-- for each frequency vector s ∈ ℤ_k^n. Because the characters form an
-- orthonormal basis, every function admits the Fourier expansion
--     f(x) = ∑_s f̂(s) · χ_s(x)
-- and the Parseval identity
--     ∑_s |f̂(s)|² = ‖f‖₂²
-- expresses conservation of L² energy. The convolution theorem
--     (f*g)^(s) = f̂(s) · ĝ(s)
-- converts convolution in the spatial domain to pointwise multiplication
-- in the frequency domain.
--
-- These are the direct analogues of the identities in BoolFourier.lean,
-- generalized from ℝ-valued functions on F₂ⁿ to ℂ-valued functions on ℤ_k^n.
-- The main structural difference is the use of complex norms |·| and
-- conjugation in place of real squaring.
-- ============================================================================
section FOURIER_COEFFICIENTS

variable {k : ℕ} [NeZero k] {n : ℕ}

-- f-hat(s) = ⟨f, χ_s⟩
noncomputable def fourier_coeff (f : ZkFun k n) (s : ZkVec k n) : ℂ :=
  inner_product f (char_s s)

-- (χ_s)-hat(s) = 1
lemma fourier_coeff_char_self (s : ZkVec k n) :
    fourier_coeff (char_s s) s = 1 := inner_product_char_self s

-- (χ_s)-hat(t) = 0 for s ≠ t
lemma fourier_coeff_char_of_ne {s t : ZkVec k n} (hst : s ≠ t) :
    fourier_coeff (char_s s) t = 0 := inner_product_char_nonself hst

-- f(x) = ∑_s f-hat(s) χ_s(x)
private lemma fourier_expansion_aux_h_dual_orthogonality {k : Nat} [inst : NeZero k] {n : Nat} (x y : ZkVec k n) : ∑ s : ZkVec k n, char_s s (x - y) = if x = y then (k : ℂ) ^ n else 0 := by
  split_ifs with h; simp_all +decide ;
  · exact mod_cast card_ZkVec k n ▸ rfl;
  · convert expectation_char_nontrivial ( show x - y ≠ 0 from sub_ne_zero.mpr h ) |> fun h => mul_eq_zero_of_right ( k ^ n : ℂ ) h using 1;
    unfold expectation; norm_num [ mul_div_cancel₀, NeZero.ne ] ;
    apply Finset.sum_bij (fun s _ => s);
    · exact fun _ _ => Finset.mem_univ _;
    · aesop;
    · aesop;
    · intro a _; unfold char_s; simp +decide [ mul_comm, zkDot ] ;

private lemma fourier_expansion_aux_h_exchange_order {k : Nat} [inst : NeZero k] {n : Nat} (f : ZkFun k n) (x : ZkVec k n) (h_dual_orthogonality : ∀ (x y : ZkVec k n), ∑ s : ZkVec k n, char_s s (x - y) = if x = y then (k : ℂ) ^ n else 0) : ∑ s : ZkVec k n, (∑ y : ZkVec k n, f y * starRingEnd ℂ (char_s s y) / (k : ℂ) ^ n) * char_s s x = ∑ y : ZkVec k n, f y * (∑ s : ZkVec k n, char_s s (x - y)) / (k : ℂ) ^ n := by
  simp +decide only [div_eq_mul_inv, mul_comm, mul_left_comm, Finset.mul_sum _ _ _];
  rw [ Finset.sum_comm ];
  simp +decide [ char_s_conj, sub_eq_add_neg ];
  simp +decide [ char_s_add ];
  simp +decide [ char_s, zkDot ];
  simp +decide [ ZkVec, mul_neg ];

lemma fourier_expansion (f : ZkFun k n) (x : ZkVec k n) :
    f x = ∑ s : ZkVec k n, fourier_coeff f s * char_s s x := by
      -- Swap the order of summation (Fubini for finite sums).
      let h_exchange_order : ∑ s : ZkVec k n, (∑ y : ZkVec k n, f y * starRingEnd ℂ (char_s s y) / (k : ℂ) ^ n) * char_s s x = ∑ y : ZkVec k n, f y * (∑ s : ZkVec k n, char_s s (x - y)) / (k : ℂ) ^ n := (fourier_expansion_aux_h_exchange_order f x (fourier_expansion_aux_h_dual_orthogonality))
      -- Apply dual orthogonality: the sum over s collapses to k^n · 𝟙[x = y],
      -- leaving only the y = x term, which gives f(x).
      simp_all +decide [ fourier_coeff, inner_product , (fourier_expansion_aux_h_dual_orthogonality), h_exchange_order];
      unfold expectation; simp_all +decide [ Finset.sum_div _ _ _ , (fourier_expansion_aux_h_dual_orthogonality), h_exchange_order] ;
      simp +decide [ div_eq_mul_inv, mul_comm, NeZero.ne ]

-- ∑_s |f-hat(s)|^2 = ∥f∥_2^2
private lemma parseval_identity_aux_h_L2_norm_sq {k : Nat} [inst : NeZero k] {n : Nat} (f : ZkFun k n) : L2_norm_sq f = (∑ x : ZkVec k n, f x * starRingEnd ℂ (f x)) / (k : ℂ) ^ n := by
  norm_num [ Complex.mul_conj, Complex.normSq_eq_norm_sq, L2_norm_sq ];

private lemma parseval_identity_aux_h_fourier_coeff {k : Nat} [inst : NeZero k] {n : Nat} (f : ZkFun k n) (h_L2_norm_sq : L2_norm_sq f = (∑ x : ZkVec k n, f x * starRingEnd ℂ (f x)) / (k : ℂ) ^ n) : ∑ s : ZkVec k n, ‖fourier_coeff f s‖ ^ 2 = (∑ s : ZkVec k n, fourier_coeff f s * starRingEnd ℂ (fourier_coeff f s)) := by
  simp +decide [ Complex.mul_conj, Complex.normSq_eq_norm_sq ];

private lemma parseval_identity_aux_h_fourier_coeff_def {k : Nat} [inst : NeZero k] {n : Nat} (f : ZkFun k n) (h_L2_norm_sq : L2_norm_sq f = (∑ x : ZkVec k n, f x * starRingEnd ℂ (f x)) / (k : ℂ) ^ n) (h_fourier_coeff : ∑ s : ZkVec k n, ‖fourier_coeff f s‖ ^ 2 = (∑ s : ZkVec k n, fourier_coeff f s * starRingEnd ℂ (fourier_coeff f s))) (s : ZkVec k n) : fourier_coeff f s = (∑ x : ZkVec k n, f x * starRingEnd ℂ (char_s s x)) / (k : ℂ) ^ n := by
  exact Complex.ext rfl rfl;

private lemma parseval_identity_aux_h_substitute {k : Nat} [inst : NeZero k] {n : Nat} (f : ZkFun k n) (h_L2_norm_sq : L2_norm_sq f = (∑ x : ZkVec k n, f x * starRingEnd ℂ (f x)) / (k : ℂ) ^ n) (h_fourier_coeff : ∑ s : ZkVec k n, ‖fourier_coeff f s‖ ^ 2 = (∑ s : ZkVec k n, fourier_coeff f s * starRingEnd ℂ (fourier_coeff f s))) : ∑ s : ZkVec k n, fourier_coeff f s * starRingEnd ℂ (fourier_coeff f s) = ∑ x : ZkVec k n, (∑ s : ZkVec k n, fourier_coeff f s * char_s s x) * starRingEnd ℂ (f x) / (k : ℂ) ^ n := by
  simp +decide only [(parseval_identity_aux_h_fourier_coeff_def f h_L2_norm_sq h_fourier_coeff), sum_div];
  simp +decide [ div_eq_mul_inv, mul_assoc, mul_comm, mul_left_comm, Finset.mul_sum _ _ _ ];
  rw [ Finset.sum_comm ];

private lemma parseval_identity_aux_h_inner_sum {k : Nat} [inst : NeZero k] {n : Nat} (f : ZkFun k n) (h_L2_norm_sq : L2_norm_sq f = (∑ x : ZkVec k n, f x * starRingEnd ℂ (f x)) / (k : ℂ) ^ n) (h_fourier_coeff : ∑ s : ZkVec k n, ‖fourier_coeff f s‖ ^ 2 = (∑ s : ZkVec k n, fourier_coeff f s * starRingEnd ℂ (fourier_coeff f s))) (h_substitute : ∑ s : ZkVec k n, fourier_coeff f s * starRingEnd ℂ (fourier_coeff f s) = ∑ x : ZkVec k n, (∑ s : ZkVec k n, fourier_coeff f s * char_s s x) * starRingEnd ℂ (f x) / (k : ℂ) ^ n) (x : ZkVec k n) : ∑ s : ZkVec k n, fourier_coeff f s * char_s s x = f x := by
  exact Eq.symm (fourier_expansion f x);

private lemma parseval_identity_tail_h_fourier_coeff {k : Nat} [inst : NeZero k] {n : Nat} (f : ZkFun k n) (h_fourier_coeff : ↑(∑ s, ‖fourier_coeff f s‖ ^ 2) = ∑ s, fourier_coeff f s * (starRingEnd ℂ) (fourier_coeff f s)) : ∑ s, ‖fourier_coeff f s‖ ^ 2 = L2_norm_sq f := by
  -- Substitute the Fourier expansion f(x) = ∑_s f̂(s) χ_s(x) into the
  -- inner sum, so that ∑_s f̂(s) · conj(f̂(s)) becomes a double sum
  -- that collapses by orthogonality.

  -- Use the Fourier expansion to replace the inner sum with f(x).

  simp_all +decide [ ← Finset.sum_div _ _ _ , ((parseval_identity_aux_h_substitute f ((parseval_identity_aux_h_L2_norm_sq f)) h_fourier_coeff)), ((parseval_identity_aux_h_inner_sum f ((parseval_identity_aux_h_L2_norm_sq f)) h_fourier_coeff ((parseval_identity_aux_h_substitute f ((parseval_identity_aux_h_L2_norm_sq f)) h_fourier_coeff))))];
  exact_mod_cast h_fourier_coeff.trans ((parseval_identity_aux_h_L2_norm_sq f)).symm


lemma parseval_identity (f : ZkFun k n) :
    ∑ s : ZkVec k n, ‖fourier_coeff f s‖ ^ 2 = L2_norm_sq f := by
      -- Rewrite the L² norm using the Hermitian product: ‖f‖₂² = E[f · f̄].

      -- Rewrite ∑|f̂(s)|² using the Hermitian product: |f̂(s)|² = f̂(s) · conj(f̂(s)).
      exact (parseval_identity_tail_h_fourier_coeff f ((parseval_identity_aux_h_fourier_coeff f ((parseval_identity_aux_h_L2_norm_sq f)))))









-- (f*g)-hat(s) = f-hat(s) g-hat(s)
lemma fourier_coeff_convolution (f g : ZkFun k n) (s : ZkVec k n) :
    fourier_coeff (convolution f g) s =
    fourier_coeff f s * fourier_coeff g s := by
      unfold fourier_coeff convolution;
      unfold inner_product expectation;
      -- Rearrange sums and apply Fubini (swap order of summation).
      simp +decide only [← sum_div, div_mul_eq_mul_div, sum_mul];
      rw [ Finset.sum_comm ];
      simp +decide [ div_eq_mul_inv, mul_assoc, mul_comm, mul_left_comm, Finset.mul_sum _ _ _ ];
      -- Reindex via the bijection y ↦ y + x and use χ_s(x+y) = χ_s(x) · χ_s(y).
      refine' Finset.sum_congr rfl fun x _ => _;
      rw [ ← Equiv.sum_comp ( Equiv.addRight x ) ] ; simp +decide [ mul_comm, mul_left_comm, char_s_add ]

end FOURIER_COEFFICIENTS

end ZkFourier
