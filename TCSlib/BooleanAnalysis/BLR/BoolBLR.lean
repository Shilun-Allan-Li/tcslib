/-
Copyright (c) 2026 Prastik Mohanraj. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prastik Mohanraj
-/

import Mathlib
import TCSlib.BooleanAnalysis.BLR.BoolFourier
open Finset BoolFourier

namespace BoolBLR

/-
# BoolBLR.lean

BLR (Blum–Luby–Rubinfeld) linearity test on the Boolean hypercube. Shows that a function
is linear iff its ±1 lift is a Fourier character, and derives soundness: any function
ε-far from linear functions fails the test with probability ≥ ε.

* **SECTION 1: LINEAR_FUNCTIONS** — Definition of Boolean linearity and its equivalence to Fourier characters
* **SECTION 2: BLR_TEST** — The BLR acceptance probability and Fourier-analytic soundness analysis
* **SECTION 3: BLR_RESULTS** — Completeness (linear functions pass) and soundness (ε-far functions fail)
-/

-- ============================================================================
-- SECTION 1: LINEAR_FUNCTIONS
-- ----------------------------------------------------------------------------
-- A function f : F_2^n → F_2 is linear iff f(x ⊕ y) = f(x) ⊕ f(y).
-- Equivalently, f is linear iff its ±1 lift (-1)^f is exactly some character χ_S.
-- This identification is what lets us pose "BLR linearity testing" as a Fourier
-- problem: testing closeness to a linear function = testing concentration of
-- Fourier mass on a single character.
-- ============================================================================
section LINEAR_FUNCTIONS

-- a linear function satisfies f(x + y) = f(x) + f(y) for all x, y
def is_linear_bool {n : ℕ} (f : hypercube n → Bool) : Prop :=
  ∀ x y, f (xor_vec x y) = Bool.xor (f x) (f y)

-- Lift a Boolean function to a real-valued ±1 function via (-1)^{f(x)}.
def lift_pm1 (f : hypercube n → Bool) : BoolFun n :=
  fun x => BoolToPM1 (f x)

-- dist (f, g) = Pr [ f(x) ≠ g(x) ]
noncomputable def bool_dist {n : ℕ}
    (f g : hypercube n → Bool) : ℝ :=
  expectation (fun x =>
    if f x = g x then 0 else 1)

-- f is epsilon-far from any linear function if for all linear g, dist(f, g) ≥ ε
def epsilon_far_from_linear {n : ℕ}
    (f : hypercube n → Bool) (ε : ℝ) : Prop :=
  0 ≤ ε ∧ ε ≤ 1 ∧
  ∀ g : hypercube n → Bool,
    is_linear_bool g →
      bool_dist f g ≥ ε

-- f is linear if and only if (-1)^f = χ_S for some S
private lemma linear_bool_iff_character_aux_h_fx_1 {n : ℕ} (f : BoolFourier.hypercube n → Bool) (hf : is_linear_bool f) :
    ∀ (s : Finset (Fin n)),
  (f fun i => if i ∈ s then true else false) =
    if (∑ i ∈ s, if (f fun j => if j = i then true else false) = true then 1 else 0) % 2 = 0 then false else true :=
  by
  intro s;
  induction s using Finset.induction <;> simp_all +decide ;
  · -- Base case s = ∅: f(0,…,0) = false, computed using linearity at (0,0).
    convert (hf ( fun _ => false ) ( fun _ => false )) using 1;
    simp +decide;
  · -- Inductive step: peel off one element using the linearity hypothesis hf.
    rename_i i s hi hs; specialize hf ( fun j => decide ( j = i ) ) ( fun j => decide ( j ∈ s ) ) ; simp_all +decide [ Finset.filter_insert ] ;
    convert hf using 1;
    · congr! 2;
      by_cases hi : ‹Fin n› = i <;> by_cases hs : ‹Fin n› ∈ s <;> simp +decide [ hi, hs, xor_vec ];
      · assumption;
      · assumption;
    · grind +splitImp;

private lemma linear_bool_iff_character_aux_h_fx_2 {n : ℕ} (f : BoolFourier.hypercube n → Bool) (hf : is_linear_bool f) (x : BooleanAnalysis.BoolCube n) :
    f x =
  if (∑ i with x i = true, if (f fun j => if j = i then true else false) = true then 1 else 0) % 2 = 0 then false
  else true :=
  by
  -- More general claim by induction on the support set s.

  -- Specialize to s = support of x.
  convert (linear_bool_iff_character_aux_h_fx_1 f hf) ( Finset.univ.filter fun i => x i = true ) using 2 ; aesop;

private lemma linear_bool_iff_character_aux_h_char {n : ℕ} (S : Finset (Fin n)) (x : BoolFourier.hypercube n) (y : BoolFourier.hypercube n) :
    BoolFourier.char_S S (BoolFourier.xor_vec x y) = BoolFourier.char_S S x * BoolFourier.char_S S y :=
  by
  simp only [char_S, BooleanAnalysis.chiS, ← Finset.prod_mul_distrib]
  congr 1 ; ext i ; simp [xor_vec, BoolToPM1_xor]

private lemma linear_bool_iff_character_aux_h_eq {n : ℕ} (f : BoolFourier.hypercube n → Bool) (S : Finset (Fin n)) (hS : lift_pm1 f = BoolFourier.char_S S) (x : BoolFourier.hypercube n) (y : BoolFourier.hypercube n) (h_char : BoolFourier.char_S S (BoolFourier.xor_vec x y) = BoolFourier.char_S S x * BoolFourier.char_S S y) :
    BoolFourier.BoolToPM1 (f (BoolFourier.xor_vec x y)) = BoolFourier.BoolToPM1 (f x ^^ f y) :=
  by
  unfold lift_pm1 at hS;
  rw [congr_fun hS (xor_vec x y), h_char, ← congr_fun hS x, ← congr_fun hS y, ← BoolToPM1_xor]

private lemma linear_bool_iff_character_aux_h_fx {n : ℕ} (f : hypercube n → Bool) (hf : is_linear_bool f) (x : BooleanAnalysis.BoolCube n) :
    f x =
  if (∑ i with x i = true, if (f fun j => if j = i then true else false) = true then 1 else 0) % 2 = 0 then false
  else true :=
  (linear_bool_iff_character_aux_h_fx_2 f hf x)

private lemma linear_bool_iff_character_aux_h_eq_h {n : ℕ} (f : hypercube n → Bool) (S : Finset (Fin n)) (hS : lift_pm1 f = char_S S) (x : hypercube n) (y : hypercube n) :
    BoolToPM1 (f (xor_vec x y)) = BoolToPM1 (f x ^^ f y) :=
  (linear_bool_iff_character_aux_h_eq f S hS x y (linear_bool_iff_character_aux_h_char S x y))

lemma linear_bool_iff_character {n : ℕ} (f : hypercube n → Bool) :
  is_linear_bool f ↔ ∃ S, lift_pm1 f = char_S S := by
  classical
  refine' ⟨ fun hf => _, _ ⟩;
  -- (=>) Given linearity, construct S explicitly as the support of f on basis vectors.
  · use Finset.univ.filter fun i => f ( fun j => if j = i then true else false ) = true;
    funext x;
    -- Express f(x) in terms of f on basis vectors using linearity:
    -- f(x) = ⨁_{i : x_i = true} f(e_i).
    let h_fx : f x = if (∑ i ∈ Finset.univ.filter (fun i => x i), if f (fun j => if j = i then true else false) then 1 else 0) % 2 = 0 then false else true := (linear_bool_iff_character_aux_h_fx f hf x)

    -- Now compare lift_pm1 f x with the character: both equal (-1)^{(parity)}.
    unfold lift_pm1 char_S; simp +decide [ h_fx ] ; simp only [BooleanAnalysis.chiS] ;
    rw [ Finset.prod_congr rfl fun i hi => show BoolToPM1 ( x i ) = if x i = true then -1 else 1 from by cases x i <;> rfl ] ; simp +decide [ Finset.prod_ite ] ; ring_nf;
    -- Two cases on parity, both check by hand.
    cases Nat.mod_two_eq_zero_or_one ( Finset.card ( Finset.filter ( fun i => ( f fun j => decide ( j = i ) ) = true ) ( Finset.filter ( fun i => x i = true ) Finset.univ ) ) ) <;> simp +decide [ *, h_fx];
    · simp_all +decide [h_fx, Finset.filter_filter];
      simp_all +decide [ and_comm , h_fx];
      rw [ ← Nat.mod_add_div ( Finset.card _ ) 2, ‹Finset.card _ % 2 = 0› ] ; norm_num [ pow_add, pow_mul ];
    · simp_all +decide [h_fx, Finset.filter_filter];
      simp_all +decide [ and_comm , h_fx];
      rw [ ← Nat.mod_add_div ( Finset.card _ ) 2, ‹Finset.card _ % 2 = 1› ] ; norm_num [ pow_add, pow_mul, BoolToPM1 ];
  -- (<=) If lift_pm1 f = χ_S, then f is linear via the multiplicativity of χ_S.
  · rintro ⟨ S, hS ⟩ x y;
    -- The key fact: χ_S(x ⊕ y) = χ_S(x) χ_S(y), since BoolToPM1 turns XOR into multiplication.
    unfold lift_pm1 at hS;
    -- Since (-1) is injective on Bool, equality of ±1 lifts gives equality of bits.
    let h_eq : BoolToPM1 (f (xor_vec x y)) = BoolToPM1 (Bool.xor (f x) (f y)) := (linear_bool_iff_character_aux_h_eq_h f S hS x y)

    cases h1 : f (xor_vec x y) <;> cases h2 : f x <;> cases h3 : f y <;>
      simp_all [Bool.xor, (linear_bool_iff_character_aux_h_char S x y)] <;> (simp only [*] at h_eq; norm_num at h_eq)

end LINEAR_FUNCTIONS

-- ============================================================================
-- SECTION 2: BLR_TEST
-- ----------------------------------------------------------------------------
-- The BLR test picks two uniform random inputs x, y, queries f(x), f(y), and
-- f(x ⊕ y), and accepts iff f(x ⊕ y) = f(x) ⊕ f(y). The Fourier-analytic
-- soundness analysis: the acceptance probability has the form
--     Pr[accept] = (1 + ∑_S f̂(S)^3) / 2,
-- and Parseval together with a per-coefficient bound f̂(S) ≤ 1 - 2ε (whenever f
-- is ε-far from every linear function) yields ∑_S f̂(S)^3 ≤ 1 - 2ε, and hence
-- Pr[accept] ≤ 1 - ε.
-- ============================================================================
section BLR_TEST

-- In the following comments, we interchange between {0, 1} and {-1, +1} freely

-- Pr [ BLR accepts f ] = Pr [ f(x+y) = f(x) + f(y) ]
noncomputable def BLR_accept_prob {n : ℕ} (f : hypercube n → Bool) : ℝ :=
  expectation (fun x =>
    expectation (fun y =>
      if lift_pm1 f (xor_vec x y) = lift_pm1 f x * lift_pm1 f y then 1 else 0))

-- Pr [ BLR accepts f ] = ( 1 + E [ E [ f(x) f(y) f(x + y) ] ] ) / 2
private lemma BLR_accept_prob_pm1_aux_h_eq {n : ℕ} (f : BoolFourier.hypercube n → Bool) :
    ∀ (x y : BoolFourier.hypercube n),
  (if lift_pm1 f (BoolFourier.xor_vec x y) = lift_pm1 f x * lift_pm1 f y then 1 else 0) =
    (1 + lift_pm1 f x * lift_pm1 f y * lift_pm1 f (BoolFourier.xor_vec x y)) / 2 :=
  by
  intro x y; split_ifs;
  -- Accept case: triple product is +1, so (1+1)/2 = 1.
  · cases h : f x <;> cases h' : f y <;> simp_all +decide [ lift_pm1 ];
  -- Reject case: triple product is -1, so (1-1)/2 = 0.
  · cases h : f x <;> cases h' : f y <;> cases h'' : f ( xor_vec x y ) <;> simp_all +decide [ lift_pm1 ];

lemma BLR_accept_prob_pm1 {n : ℕ} (f : hypercube n → Bool) :
  BLR_accept_prob f
  = (1 + expectation (fun x =>
        expectation (fun y =>
          lift_pm1 f x * lift_pm1 f y * lift_pm1 f (xor_vec x y)))) / 2 := by
  unfold BLR_accept_prob expectation;
  -- Pointwise, the indicator equals (1 + product of three ±1 values)/2.
  -- Push the (1 + …)/2 form through expectations.
  simp_all +decide [ Finset.sum_add_distrib, add_div , (BLR_accept_prob_pm1_aux_h_eq f)];
  norm_num [ ← Finset.sum_div _ _ _, card_hypercube ] ; ring

-- E [ E [ f(x) f(y) f(x + y) ] ] = E [ f(x) E [ f(y) f(x + y) ] ] = E [ f(x) (f * f) (x) ]
lemma triple_expectation_as_convolution {n : ℕ} (f : BoolFun n) :
  expectation (fun x =>
    expectation (fun y =>
      f x * f y * f (xor_vec x y)))
  = expectation (fun x =>
      f x * expectation (fun y => f y * f (xor_vec x y))) := by
  unfold expectation;
  simp +decide [ div_eq_mul_inv, mul_assoc, mul_comm, mul_left_comm, Finset.mul_sum _ _ _ ]

-- E [ E [ f(x) f(y) f(x + y) ] ] = ∑_S f-hat (S) ^ 3
private lemma triple_expectation_eq_cube_fourier_aux_h_convolution {n : ℕ} (f : BoolFourier.hypercube n → Bool) :
    ∀ (x : BooleanAnalysis.BoolCube n),
  BoolFourier.convolution (lift_pm1 f) (lift_pm1 f) x =
    ∑ S, BoolFourier.fourier_coeff (lift_pm1 f) S ^ 2 * BoolFourier.char_S S x :=
  by
  intro x;
  convert fourier_expansion ( BoolFourier.convolution ( lift_pm1 f ) ( lift_pm1 f ) ) x using 1;
  exact Finset.sum_congr rfl fun _ _ => by rw [ fourier_coeff_convolution ] ; ring;

private lemma triple_expectation_eq_cube_fourier_aux_h_substitute {n : ℕ} (f : BoolFourier.hypercube n → Bool) (h_convolution : ∀ (x : BooleanAnalysis.BoolCube n),
  BoolFourier.convolution (lift_pm1 f) (lift_pm1 f) x =
    ∑ S, BoolFourier.fourier_coeff (lift_pm1 f) S ^ 2 * BoolFourier.char_S S x) :
    (BoolFourier.expectation fun x => lift_pm1 f x * BoolFourier.convolution (lift_pm1 f) (lift_pm1 f) x) =
  ∑ S,
    BoolFourier.fourier_coeff (lift_pm1 f) S ^ 2 *
      BoolFourier.expectation fun x => lift_pm1 f x * BoolFourier.char_S S x :=
  by
  simp +decide only [h_convolution, Finset.mul_sum _ _ _, expectation];
  rw [ Finset.sum_comm ] ; simp +decide [ div_eq_mul_inv, mul_assoc, mul_comm, mul_left_comm, Finset.mul_sum _ _ _] ;

lemma triple_expectation_eq_cube_fourier {n : ℕ} (f : hypercube n → Bool) :
  expectation (fun x =>
    expectation (fun y =>
      lift_pm1 f x * lift_pm1 f y * lift_pm1 f (xor_vec x y)))
  = ∑ S : Finset (Fin n), (fourier_coeff (lift_pm1 f) S) ^ 3 := by
  -- Step 1: Fourier expansion of f * f, with coefficients f̂(S)^2 by BoolFourier.convolution thm.
  -- Step 2: substitute into E[f(x)·(f*f)(x)] and pull the Fourier sum out.
  -- The final step: each E[f·χ_S] = f̂(S), so f̂(S)^2 · f̂(S) = f̂(S)^3.
  convert (triple_expectation_eq_cube_fourier_aux_h_substitute f (triple_expectation_eq_cube_fourier_aux_h_convolution f)) using 2;
  unfold BoolFourier.convolution; norm_num [ mul_assoc, mul_comm, mul_left_comm, Finset.mul_sum _ _ _ ] ;
  unfold expectation; norm_num [ Finset.mul_sum _ _ _ ] ;
  simp +decide only [Finset.sum_div, Finset.mul_sum _ _ _, mul_div]

-- if f is epsilon-far from a given linear function (i.e., chi_S), then f-hat (S) ≤ 1 - 2 * ε
private lemma fourier_coeff_le_of_dist_ge_aux_h_lift_pm1 {n : ℕ} (f : BoolFourier.hypercube n → Bool) (g : BoolFourier.hypercube n → Bool) :
    ∀ (x : BooleanAnalysis.BoolCube n), lift_pm1 f x * lift_pm1 g x = 1 - 2 * if f x = g x then 0 else 1 :=
  by
  unfold lift_pm1;
  intro x; rcases f x with ( _ | _ | f ) <;> rcases g x with ( _ | _ | g ) <;> norm_num [ BoolToPM1 ] ;

lemma fourier_coeff_le_of_dist_ge
    {n : ℕ}
    (f g : hypercube n → Bool)
    (S : Finset (Fin n))
    (hchar : lift_pm1 g = char_S S)
    (hdist : bool_dist f g ≥ ε) :
    fourier_coeff (lift_pm1 f) S ≤ 1 - 2 * ε := by
  -- Reduce to f̂(S) ≤ 1 - 2 · dist(f,g).
  refine le_trans ?_ ( sub_le_sub_left ( mul_le_mul_of_nonneg_left hdist <| by norm_num ) 1 );
  unfold fourier_coeff bool_dist;
  unfold inner_product expectation;
  -- Pointwise identity: lift(f)(x)·lift(g)(x) = 1 - 2·𝟙[f(x) ≠ g(x)].
  simp_all +decide [ ← hchar, Finset.sum_ite , (fourier_coeff_le_of_dist_ge_aux_h_lift_pm1 f g)];
  ring_nf; norm_num [ card_hypercube ] ;
  norm_num [ ← mul_pow ]

-- if f is epsilon-far from all linear functions, then f-hat (S) ≤ 1 - 2 * ε for all S
lemma fourier_coeff_le_of_far_from_linear
    {n : ℕ}
    (f : hypercube n → Bool)
    (ε : ℝ)
    (hfar : epsilon_far_from_linear f ε) :
    ∀ S : Finset (Fin n),
      fourier_coeff (lift_pm1 f) S ≤ 1 - 2 * ε := by
  intro S
  -- Build a linear g whose ±1 lift equals χ_S, witnessing closeness to χ_S.
  obtain ⟨g, hg⟩ : ∃ g : hypercube n → Bool, is_linear_bool g ∧ (lift_pm1 g) = (char_S S) := by
    -- First, exhibit g as parity over coordinates in S.
    obtain ⟨g, hg⟩ : ∃ g : hypercube n → Bool, lift_pm1 g = char_S S := by
      use fun x => (S.filter (fun i => x i)).card % 2 = 1;
      funext x; simp [lift_pm1, char_S];
      -- Induction on S to compare parity-of-count vs product of (-1)^{x_i}.
      induction S using Finset.induction <;> try simp_all +decide ;
      · by_cases h : x ‹_› <;> simp_all +decide [ Finset.filter_insert ];
        · cases Nat.mod_two_eq_zero_or_one ( Finset.card ( Finset.filter ( fun i => x i = true ) ‹_› ) ) <;> simp_all +decide [ Nat.add_mod ];
          · simp only [BooleanAnalysis.chiS, Finset.prod_insert ‹_ ∉ _›, ‹x _ = true›,
                       BooleanAnalysis.boolToSign_true] ; ring
          ·
            simp only [BooleanAnalysis.chiS, Finset.prod_insert (‹_›), ‹x _ = true›,
                       BooleanAnalysis.boolToSign_true] at *
            linarith
        · simp only [BooleanAnalysis.chiS, Finset.prod_insert ‹_ ∉ _›, ‹x _ = false›,
                     BooleanAnalysis.boolToSign_false] ; ring
    -- Then use linear_bool_iff_character to conclude g is linear.
    exact ⟨ g, by exact linear_bool_iff_character g |>.2 ⟨ S, hg ⟩, hg ⟩;
  -- Apply the previous lemma using the ε-farness from this specific linear g.
  exact fourier_coeff_le_of_dist_ge f g S hg.2 ( hfar.2.2 g hg.1 )

-- if f is epsilon-far from all linear functions, then the sum of cubes term is ≤ 1 - 2 * ε
private lemma BLR_soundness_via_fourier_aux_hparseval {n : ℕ} (f : BoolFourier.hypercube n → Bool) :
    ∑ S, BoolFourier.fourier_coeff (lift_pm1 f) S ^ 2 = 1 :=
  by
  convert parseval_identity ( lift_pm1 f ) using 1;
  unfold L2_norm_sq lift_pm1;
  unfold expectation; norm_num [ BoolToPM1_sq ] ;

private lemma BLR_soundness_via_fourier_aux_h_bound {n : ℕ} (f : BoolFourier.hypercube n → Bool) (ε : ℝ) (hfar : epsilon_far_from_linear f ε) :
    ∀ (S : Finset (Fin n)),
  BoolFourier.fourier_coeff (lift_pm1 f) S ^ 3 ≤ BoolFourier.fourier_coeff (lift_pm1 f) S ^ 2 * (1 - 2 * ε) :=
  by
  exact fun S => by nlinarith only [ show fourier_coeff ( lift_pm1 f ) S ≤ 1 - 2 * ε by exact fourier_coeff_le_of_far_from_linear f ε hfar S ] ;

lemma BLR_soundness_via_fourier {n : ℕ}
    (f : hypercube n → Bool)
    (ε : ℝ)
    (hfar : epsilon_far_from_linear f ε) :
  ∑ S : Finset (Fin n), (fourier_coeff (lift_pm1 f) S) ^ 3
    ≤ 1 - 2 * ε := by
    -- Parseval for ±1-valued lift_pm1: each (lift_pm1 f)(x)^2 = 1, so ‖f‖_2^2 = 1.
    -- f̂(S)^3 = f̂(S)^2 · f̂(S) ≤ f̂(S)^2 · (1 - 2ε), since f̂(S)^2 ≥ 0 and f̂(S) ≤ 1 - 2ε.
    -- Sum the per-S bound and apply Parseval.
    convert Finset.sum_le_sum fun S _ => (BLR_soundness_via_fourier_aux_h_bound f ε hfar) S using 1 ; rw [ ← Finset.sum_mul _ _ _ ] ; simp_all only [one_mul, (BLR_soundness_via_fourier_aux_hparseval f)];

end BLR_TEST

-- ============================================================================
-- SECTION 3: BLR_RESULTS
-- ----------------------------------------------------------------------------
-- The main theorems for the BLR linearity test:
--   • Completeness: a truly linear function passes BLR with probability 1.
--   • Soundness:    a function ε-far from every linear function fails with
--                   probability at least ε (i.e., passes with probability ≤ 1-ε).
-- Together these say BLR distinguishes linear functions from those ε-far from
-- linear with O(1/ε) queries — the celebrated "BLR linearity test" guarantee.
-- ============================================================================
section BLR_RESULTS

-- Pr [ BLR accepts f ] = 1 if f is linear
private lemma BLR_completeness_aux_h_linear {n : ℕ} (f : BoolFourier.hypercube n → Bool) (hlin : is_linear_bool f) :
    ∀ (x y : BoolFourier.hypercube n), f (BoolFourier.xor_vec x y) = (f x ^^ f y) :=
  by
  exact hlin;

private lemma BLR_completeness_aux_h_lift_linear {n : ℕ} (f : BoolFourier.hypercube n → Bool) (h_linear : ∀ (x y : BoolFourier.hypercube n), f (BoolFourier.xor_vec x y) = (f x ^^ f y)) :
    ∀ (x y : BoolFourier.hypercube n), lift_pm1 f (BoolFourier.xor_vec x y) = lift_pm1 f x * lift_pm1 f y :=
  by
  intros x y; exact (by
  convert BoolToPM1_xor ( f x ) ( f y ) using 1;
  exact h_linear x y ▸ rfl);

lemma BLR_completeness {n : ℕ}
    (f : hypercube n → Bool)
    (hlin : is_linear_bool f) :
  BLR_accept_prob f = 1 := by
  -- Restate linearity in convenient form.
  -- Lift to the ±1 world: linearity becomes multiplicativity.
  unfold BLR_accept_prob;
  -- Each indicator becomes 1, and 2^n · 2^n / 2^n / 2^n = 1.
  unfold expectation; norm_num [ (BLR_completeness_aux_h_lift_linear f (BLR_completeness_aux_h_linear f hlin)) ] ;

-- Pr [ BLR accepts f ] ≤ 1 - ε if f is ε-far from any linear function
lemma BLR_soundness {n : ℕ}
    (f : hypercube n → Bool)
    (ε : ℝ)
    (hfar : epsilon_far_from_linear f ε) :
  BLR_accept_prob f ≤ 1 - ε := by
  rw [BLR_accept_prob_pm1];
  -- Combine the cube-sum identity and the soundness bound; linarith finishes.
  linarith [ BLR_soundness_via_fourier f ε hfar, triple_expectation_eq_cube_fourier f ]

end BLR_RESULTS

end BoolBLR
