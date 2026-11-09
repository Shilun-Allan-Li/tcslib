/-
Copyright (c) 2026 TCSlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Owen McGinty
-/

import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.MeasureTheory.Integral.MeanInequalities
import TCSlib.BooleanAnalysis.Hypercontractivity.Cube.Decomposition

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Fourth-moment cube hypercontractivity

Coordinate decomposition and moment estimates for the forward noise operator.

## Main definitions

Shared definitions are imported; local technical helpers accompany their proofs.

## Main results

* `chiS_snoc_castSucc`.
* `chiS_snoc_with_last`.
* `finset_fin_succ_sum_partition`.
* `card_image_castSucc`.
* `card_image_castSucc_union_last`.
* `noiseOp_snoc`.
* `fourth_moment_noise_decomp`.
* `hypercontractivity_algebra'`.
* `hypercontractivity_2_4`.
* `innerProduct_le_L43_L4`.
* `hypercontractivity_4_div_3_2`.

## References

* [OD14] Ryan O'Donnell, *Analysis of Boolean Functions*, Cambridge University Press,
  2014, §§9.3–10.1.
-/

open BooleanAnalysis MeasureTheory Set Filter ProbabilityTheory Real
open scoped BigOperators ENNReal Classical

namespace BooleanAnalysis.Hypercontractivity

variable {n : ℕ}

/-! ## (2,4)-Hypercontractivity Theorem -/

/--
`χ_{S.image castSucc}(Fin.snoc x b) = χ_S(x)`: the character of a lifted set
  ignores the last coordinate.
**Source:** [OD14, Thm. 9.17 (proof)]. -/
lemma chiS_snoc_castSucc {n : ℕ} (S : Finset (Fin n)) (x : BoolCube n) (b : Bool) :
    chiS (S.image Fin.castSucc) (Fin.snoc x b) = chiS S x := by
  unfold chiS; simp_all only [Fin.castSucc_inj, implies_true, injOn_of_eq_iff_eq, Finset.prod_image, Fin.snoc_castSucc];

/--
`χ_{S.image castSucc ∪ {last n}}(Fin.snoc x b) = boolToSign b * χ_S(x)`.
**Source:** [OD14, Thm. 9.17 (proof)]. -/
lemma chiS_snoc_with_last {n : ℕ} (S : Finset (Fin n)) (x : BoolCube n) (b : Bool) :
    chiS (S.image Fin.castSucc ∪ {Fin.last n}) (Fin.snoc x b) = boolToSign b * chiS S x := by
  unfold chiS; simp +decide only [Finset.union_singleton, Finset.mem_image, Fin.castSucc_ne_last,
    and_false, exists_false, not_false_eq_true, Finset.prod_insert, Fin.snoc_last, Fin.castSucc_inj,
    implies_true, injOn_of_eq_iff_eq, Finset.prod_image, Fin.snoc_castSucc] ;

/--
Partition of `∑ S : Finset (Fin (n+1))` by membership of `Fin.last n`:
  every subset of `[n+1]` either avoids or contains the last element.

**Source:** [OD14, Thm. 9.17 (proof)].

**Proof sketch.** Partition subsets according to whether they contain the final coordinate. Each
part is in bijection with subsets of the smaller coordinate set, by lifting alone or by lifting
and adjoining the final coordinate. Sum over these disjoint classes.
-/
lemma finset_fin_succ_sum_partition {n : ℕ} (φ : Finset (Fin (n + 1)) → ℝ) :
    ∑ S : Finset (Fin (n + 1)), φ S =
    ∑ T : Finset (Fin n), φ (T.image Fin.castSucc) +
    ∑ T : Finset (Fin n), φ (T.image Fin.castSucc ∪ {Fin.last n}) := by
  -- We partition Finset (Fin (n+1)) by whether Fin.last n is in the set.
  have h_partition : Finset.univ = Finset.image (fun T : Finset (Fin n) => T.image Fin.castSucc) (Finset.univ : Finset (Finset (Fin n))) ∪ Finset.image (fun T : Finset (Fin n) => T.image Fin.castSucc ∪ {Fin.last n}) (Finset.univ : Finset (Finset (Fin n))) := by
    ext S;
    by_cases h : Fin.last n ∈ S <;> simp +decide only [Finset.mem_univ, Finset.union_singleton,
      Finset.mem_union, Finset.mem_image, true_and, true_iff];
    · refine Or.inr ⟨ Finset.univ.filter fun i => Fin.castSucc i ∈ S, ?_ ⟩;
      ext i; simp [Finset.mem_insert, Finset.mem_image];
      exact ⟨ fun hi => hi.elim ( fun hi => hi.symm ▸ h ) fun ⟨ a, ha₁, ha₂ ⟩ => ha₂ ▸ ha₁, fun hi => if hi' : i = Fin.last n then Or.inl hi' else Or.inr ⟨ ⟨ i.val, lt_of_le_of_ne ( Fin.le_last _ ) ( by simpa [ Fin.ext_iff ] using hi' ) ⟩, by simpa [ Fin.ext_iff ] using hi, rfl ⟩ ⟩;
    · refine' Or.inl ⟨ Finset.univ.filter fun i => Fin.castSucc i ∈ S, _ ⟩;
      ext i; simp [Finset.mem_image];
      exact ⟨ fun ⟨ a, ha₁, ha₂ ⟩ => ha₂ ▸ ha₁, fun hi => by cases i using Fin.lastCases <;> aesop ⟩;
  rw [ h_partition, Finset.sum_union ] <;> norm_num [ Finset.disjoint_right ];
  · rw [ Finset.sum_image, Finset.sum_image ];
    · intro T hT T' hT' h_eq; simp_all +decide [ Finset.ext_iff ] ;
      intro a; specialize h_eq ( Fin.castSucc a ) ; aesop;
    · intro T hT T' hT' h_eq; simp_all +decide [ Finset.ext_iff ] ;
      intro a; specialize h_eq ( Fin.castSucc a ) ; aesop;
  · intro a x H; replace H := Finset.ext_iff.mp H ( Fin.last n ) ; simp +decide at H;

/-- Cardinality of a lifted set: `|S.image castSucc| = |S|`.
**Source:** [OD14, Thm. 9.17 (proof)]. -/
lemma card_image_castSucc {n : ℕ} (S : Finset (Fin n)) :
    (S.image Fin.castSucc).card = S.card := by
  exact Finset.card_image_of_injective S (Fin.castSucc_injective n)

/--
Cardinality: `|S.image castSucc ∪ {last n}| = |S| + 1`.

**Source:** [OD14, Thm. 9.17 (proof)]. -/
lemma card_image_castSucc_union_last {n : ℕ} (S : Finset (Fin n)) :
    (S.image Fin.castSucc ∪ {Fin.last n}).card = S.card + 1 := by
  rw [ Finset.card_union, Finset.card_image_of_injective ] <;> norm_num [ Function.Injective ]

/--
The noise operator decomposes along the last coordinate:
  `T_ρ f(snoc x b) = T_ρ(avgLast f)(x) + boolToSign(b) · ρ · T_ρ(diffLast f)(x)`.

**Source:** [OD14, Thm. 9.17 (proof)]. -/
lemma noiseOp_snoc {n : ℕ} (ρ : ℝ) (f : BooleanFunc (n + 1)) (x : BoolCube n) (b : Bool) :
    noiseOp ρ f (Fin.snoc x b) =
    noiseOp ρ (avgLast f) x + boolToSign b * ρ * noiseOp ρ (diffLast f) x := by
  convert finset_fin_succ_sum_partition ( fun S ↦ ρ ^ S.card * BooleanAnalysis.fourierCoeff f S * chiS S ( Fin.snoc x b ) ) using 1;
  congr! 1;
  · refine' Finset.sum_congr rfl fun T _ => _;
    rw [ ← fourierCoeff_avgLast ];
    rw [ card_image_castSucc, chiS_snoc_castSucc ];
  · rw [ show noiseOp ρ ( diffLast f ) x = ∑ T : Finset ( Fin n ), ρ ^ T.card * BooleanAnalysis.fourierCoeff ( diffLast f ) T * chiS T x from rfl ];
    rw [ Finset.mul_sum _ _ _ ] ; refine' Finset.sum_congr rfl fun T hT => _ ; rw [ fourierCoeff_diffLast ] ; rw [ card_image_castSucc_union_last ] ; ring_nf;
    rw [ chiS_snoc_with_last ] ; ring

/--
Fourth moment decomposition with the noise operator.
**Source:** [OD14, Thm. 9.17 (proof), specialized to `q = 4`]. -/
lemma fourth_moment_noise_decomp {n : ℕ} (ρ : ℝ) (f : BooleanFunc (n + 1)) :
    expect (fun x => (noiseOp ρ f x) ^ 4) =
    expect (fun x => (noiseOp ρ (avgLast f) x) ^ 4) +
    6 * ρ ^ 2 * expect (fun x => (noiseOp ρ (avgLast f) x) ^ 2 * (noiseOp ρ (diffLast f) x) ^ 2) +
    ρ ^ 4 * expect (fun x => (noiseOp ρ (diffLast f) x) ^ 4) := by
  field_simp;
  convert fourth_moment_decomp ( fun x => noiseOp ρ f x ) using 2;
  · unfold avgLast diffLast; ring_nf;
    unfold restrictLast; norm_num [ noiseOp_snoc ] ; ring_nf;
    unfold avgLast diffLast; norm_num [ mul_assoc ] ;
    unfold restrictLast; norm_num [ mul_assoc, mul_comm, mul_left_comm, Finset.mul_sum _ _ _ ] ; ring_nf;
    unfold expect; norm_num [ mul_assoc, mul_comm, mul_left_comm, Finset.mul_sum _ _ _ ] ;
  · unfold diffLast;
    unfold restrictLast; norm_num [ noiseOp_snoc ] ; ring_nf;
    unfold diffLast; norm_num [ expect ] ; ring_nf;
    unfold restrictLast; norm_num [ mul_assoc, mul_comm, mul_left_comm, Finset.mul_sum _ _ _ ] ;

/-- Key algebraic inequality: under `ρ² ≤ 1/3`, the recurrence closes.
**Source:** [OD14, Thm. 9.17 (proof), specialized to `q = 4`].

**Proof sketch.** The hypotheses give C² ≤ a²b², and a,b ≥ 0 therefore imply C ≤ ab. Substitute
this and the bounds on A and B, then use ρ² ≤ 1/3 to bound the mixed coefficient by 2 and the
final coefficient by 1, obtaining (a + b)².
-/
lemma hypercontractivity_algebra' {a b A B C ρ : ℝ}
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hB_nn : 0 ≤ B)
    (hA_bound : A ≤ a ^ 2) (hB_bound : B ≤ b ^ 2)
    (hC_bound : C ^ 2 ≤ A * B) (hρ : ρ ^ 2 ≤ 1 / 3) :
    A + 6 * ρ ^ 2 * C + ρ ^ 4 * B ≤ (a + b) ^ 2 := by
    /- Helper: C² ≤ a²b² and C ≥ 0 implies C ≤ ab (for a,b ≥ 0). -/
  have sq_le_sq_mul_of_nonneg {C a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b)
    (h : C ^ 2 ≤ a ^ 2 * b ^ 2) : C ≤ a * b := by
    nlinarith [ mul_nonneg ha hb ]
  /- Helper: a² + 6ρ²ab + ρ⁴b² ≤ (a+b)² when ρ² ≤ 1/3 and a,b ≥ 0. -/
  have hypercontractivity_algebra_simple {a b ρ : ℝ}
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hρ : ρ ^ 2 ≤ 1 / 3) :
    a ^ 2 + 6 * ρ ^ 2 * (a * b) + ρ ^ 4 * b ^ 2 ≤ (a + b) ^ 2 := by
    nlinarith [ sq_nonneg ( a - b ), mul_nonneg ha hb, mul_le_mul_of_nonneg_left hρ ( sq_nonneg a ), mul_le_mul_of_nonneg_left hρ ( sq_nonneg b ) ]

  have hC_le : C ≤ a * b := by
    apply sq_le_sq_mul_of_nonneg ha hb
    calc C ^ 2 ≤ A * B := hC_bound
      _ ≤ a ^ 2 * b ^ 2 := mul_le_mul hA_bound hB_bound hB_nn (sq_nonneg a)
  calc A + 6 * ρ ^ 2 * C + ρ ^ 4 * B
      ≤ a ^ 2 + 6 * ρ ^ 2 * (a * b) + ρ ^ 4 * b ^ 2 := by
        have h2 : 6 * ρ ^ 2 * C ≤ 6 * ρ ^ 2 * (a * b) :=
          mul_le_mul_of_nonneg_left hC_le (by positivity)
        have h3 : ρ ^ 4 * B ≤ ρ ^ 4 * b ^ 2 :=
          mul_le_mul_of_nonneg_left hB_bound (by positivity)
        linarith
    _ ≤ (a + b) ^ 2 := hypercontractivity_algebra_simple ha hb hρ

/--
**The (2,4)-Hypercontractivity Theorem** (Bonami–Beckner):
For any Boolean function `f : {0,1}ⁿ → ℝ` and noise parameter `ρ` with `ρ² ≤ 1/3`
(i.e., `|ρ| ≤ 1/√3`),
  `𝔼[(T_ρ f)⁴] ≤ (𝔼[f²])²`,
or equivalently `‖T_ρ f‖₄ ≤ ‖f‖₂`.
**Source:** [OD14, Thm. 9.17], specialized to `q = 4`.

**Proof sketch.** Induct on the cube dimension, with equality on the zero-dimensional cube.
Decompose the noisy fourth moment and the original second moment along the final coordinate,
apply the induction hypothesis to both parts, and bound the mixed moment by Cauchy–Schwarz. The
algebraic recurrence closes under ρ² ≤ 1/3.
-/
theorem hypercontractivity_2_4 {n : ℕ} (ρ : ℝ) (hρ : ρ ^ 2 ≤ 1 / 3) (f : BooleanFunc n) :
    expect (fun x => (noiseOp ρ f x) ^ 4) ≤ (expect (fun x => f x ^ 2)) ^ 2 := by
  induction n with
  | zero =>
  unfold expect;
  unfold uniformWeight; norm_num;
  unfold noiseOp; ring_nf;
  erw [ Finset.sum_eq_single ∅ ] <;> norm_num;
  · unfold BooleanAnalysis.fourierCoeff;
    unfold innerProduct expect; norm_num [ Fin.eq_zero ] ;
    unfold uniformWeight; norm_num;
  · exact fun h => False.elim <| h rfl;
  · exact fun h => False.elim <| h rfl
  | succ n ih =>
    rw [fourth_moment_noise_decomp, second_moment_decomp]
    exact hypercontractivity_algebra'
      (expect_sq_nonneg (avgLast f))
      (expect_sq_nonneg (diffLast f))
      (expect_fourth_nonneg (noiseOp ρ (diffLast f)))
      (ih (avgLast f))
      (ih (diffLast f))
      (expect_cs_sq (noiseOp ρ (avgLast f)) (noiseOp ρ (diffLast f)))
      hρ

/- **The (4 / 3, 2)-Hypercontractivity Theorem** :-/

/-- Applies Hölder's inequality with exponents `4 / 3` and `4` on a Boolean cube.

**Source:** [OD14, Prop. 9.19 (proof)].

**Proof sketch.** Bound each product by the product of its absolute values and apply finite-sum
Hölder with exponents 4/3 and 4. Split the uniform weight into its 3/4 and 1/4 powers and absorb
these factors into the two moments.
-/
lemma innerProduct_le_L43_L4 (f g : BooleanFunc n) :
  innerProduct f g ≤
  (expect (fun x => |f x| ^ (4/3 : ℝ))) ^ (3/4 : ℝ) *
  (expect (fun x => |g x| ^ 4)) ^ (1/4 : ℝ) := by
  unfold innerProduct expect uniformWeight
  have h_abs : ∑ x : BoolCube n, f x * g x ≤ ∑ x : BoolCube n, |f x| * |g x| := by
    apply Finset.sum_le_sum
    intro x _
    calc
      f x * g x ≤ |f x * g x| := le_abs_self _
      _ = |f x| * |g x| := abs_mul _ _
  have h_weight_abs :
      (2⁻¹ : ℝ) ^ n * ∑ x : BoolCube n, f x * g x ≤
      (2⁻¹ : ℝ) ^ n * ∑ x : BoolCube n, |f x| * |g x| := by
    apply mul_le_mul_of_nonneg_left h_abs
    positivity
  let p : ℝ := 4/3
  let q : ℝ := 4
  have hpq : HolderConjugate p q := by
    constructor
    · norm_num -- Proves 1 < p (since 4/3 > 1)
    · norm_num
    · norm_num
  have holder_sum : ∑ x : BoolCube n, |f x| * |g x| ≤
      (∑ x, |f x| ^ p) ^ (1/p) * (∑ x, |g x| ^ q) ^ (1/q) := by
    refine inner_le_Lp_mul_Lq_of_nonneg Finset.univ hpq ?_ ?_
    · exact fun i a => abs_nonneg (f i)
    · exact fun i a => abs_nonneg (g i)
  have weight_split : (2⁻¹ : ℝ) ^ n = ((2⁻¹ : ℝ) ^ n) ^ (1/p) * ((2⁻¹ : ℝ) ^ n) ^ (1/q) := by
    have hpq_sum : (1/p : ℝ) + (1/q : ℝ) = 1 := by norm_num
    rw [← Real.rpow_add (by positivity), hpq_sum, Real.rpow_one]

  calc
    (2⁻¹ : ℝ) ^ n * ∑ x, f x * g x
      ≤ (2⁻¹ : ℝ) ^ n * ∑ x, |f x| * |g x| := h_weight_abs
    _ ≤ (2⁻¹ : ℝ) ^ n * ((∑ x, |f x| ^ p) ^ (1/p) * (∑ x, |g x| ^ q) ^ (1/q)) := by
      apply mul_le_mul_of_nonneg_left holder_sum (by positivity)
    _ = (((2⁻¹ : ℝ) ^ n) ^ (1/p) * (∑ x, |f x| ^ p) ^ (1/p)) * (((2⁻¹ : ℝ) ^ n) ^ (1/q) * (∑ x, |g x| ^ q) ^ (1/q)) := by
      calc
        (2⁻¹ : ℝ) ^ n * ((∑ x, |f x| ^ p) ^ (1/p) * (∑ x, |g x| ^ q) ^ (1/q))
          = (((2⁻¹ : ℝ) ^ n) ^ (1/p) * ((2⁻¹ : ℝ) ^ n) ^ (1/q)) * ((∑ x, |f x| ^ p) ^ (1/p) * (∑ x, |g x| ^ q) ^ (1/q)) := by nth_rw 1 [weight_split]
        _ = (((2⁻¹ : ℝ) ^ n) ^ (1/p) * (∑ x, |f x| ^ p) ^ (1/p)) * (((2⁻¹ : ℝ) ^ n) ^ (1/q) * (∑ x, |g x| ^ q) ^ (1/q)) := by ring
        _ = (((2⁻¹ : ℝ) ^ n) ^ (1/p) * (∑ x, |f x| ^ p) ^ (1/p)) * (((2⁻¹ : ℝ) ^ n) ^ (1/q) * (∑ x, |g x| ^ q) ^ (1/q)) := by ring
    _ = ((2⁻¹ : ℝ) ^ n * ∑ x, |f x| ^ p) ^ (1/p) * ((2⁻¹ : ℝ) ^ n * ∑ x, |g x| ^ q) ^ (1/q) := by
      have hfp : 0 ≤ ∑ x : BoolCube n, |f x| ^ p := Finset.sum_nonneg (fun x _ => by positivity)
      have hgq : 0 ≤ ∑ x : BoolCube n, |g x| ^ q := Finset.sum_nonneg (fun x _ => by positivity)
      rw [← Real.mul_rpow (by positivity) hfp]
      rw [← Real.mul_rpow (by positivity) hgq]
    _ = (2⁻¹ ^ n * ∑ x, (fun x => |f x| ^ (4 / 3 : ℝ)) x) ^ (3 / 4 : ℝ) * (2⁻¹ ^ n * ∑ x, (fun x => |g x| ^ 4) x) ^ (1 / 4 : ℝ) := by
      have hp_exp : (1 / p : ℝ) = 3 / 4 := by norm_num
      have hq_exp : (1 / q : ℝ) = 1 / 4 := by norm_num
      rw [hp_exp, hq_exp]
      have hq_pow : ∀ x, |g x| ^ q = |g x| ^ 4 := by
        intro x
        change |g x| ^ (4 : ℝ) = |g x| ^ (4 : ℕ)
        exact Real.rpow_natCast (|g x|) 4
      simp_rw [hq_pow]
      rfl

/-- Establishes `(4 / 3, 2)` hypercontractivity by dualizing the `(2, 4)` bound.

**Source:** [OD14, Prop. 9.19; Thm. 9.17].

**Proof sketch.** Use self-adjointness to express the squared noisy L² norm as the inner product
of the original function with its twice-noised version. Hölder and the (2,4) bound give the
original L^(4/3) norm times the noisy L² norm. Handle the zero-norm case directly and otherwise
cancel the positive noisy norm.
-/
theorem hypercontractivity_4_div_3_2 {n : ℕ} (f : BooleanFunc n) :
    (expect (fun x => (noiseOp (1 / Real.sqrt 3) f x) ^ 2)) ^ (1/2 : ℝ)
    ≤ (expect (fun x => |f x| ^ (4/3 : ℝ))) ^ (3/4 : ℝ) := by

  set ρ := 1 / Real.sqrt 3
  have hρ : ρ ^ 2 ≤ 1 / 3 := by
    dsimp [ρ]
    rw [one_div, inv_pow, Real.sq_sqrt (by positivity)]
    simp only [one_div, le_refl]

  set E_2 := expect (fun x => (noiseOp ρ f x) ^ 2)
  have hE2_nonneg : 0 ≤ E_2 := by
    unfold E_2 expect uniformWeight
    apply mul_nonneg (by positivity)
    apply Finset.sum_nonneg
    intro x _
    positivity

  by_cases h_zero : E_2 = 0
  · rw [h_zero]
    have h_zero_pow : (0 : ℝ) ^ (1 / 2 : ℝ) = 0 := by norm_num
    rw [h_zero_pow]
    -- The right side is a non-negative expectation
    apply Real.rpow_nonneg
    unfold expect uniformWeight
    apply mul_nonneg (by positivity)
    apply Finset.sum_nonneg
    intro x _
    positivity

  have hE2_pos : 0 < E_2 := lt_of_le_of_ne hE2_nonneg (Ne.symm h_zero)
  have h_inner_eq : innerProduct (noiseOp ρ f) (noiseOp ρ f) = E_2 := by
    unfold innerProduct E_2 expect
    simp_rw [sq]
  have h_abs_four : expect (fun x => |noiseOp ρ (noiseOp ρ f) x| ^ 4) = expect (fun x => noiseOp ρ (noiseOp ρ f) x ^ 4) := by
    apply congr_arg
    ext x
    calc |noiseOp ρ (noiseOp ρ f) x| ^ 4
      _ = (|noiseOp ρ (noiseOp ρ f) x| ^ 2) ^ 2 := by ring
      _ = (noiseOp ρ (noiseOp ρ f) x ^ 2) ^ 2 := by rw [sq_abs]
      _ = noiseOp ρ (noiseOp ρ f) x ^ 4 := by ring
  have hc_2_4 := hypercontractivity_2_4 ρ hρ (noiseOp ρ f)

  have h_f_L43_nonneg : 0 ≤ expect (fun x => |f x| ^ (4 / 3 : ℝ)) := by
    unfold expect uniformWeight
    apply mul_nonneg (by positivity)
    apply Finset.sum_nonneg
    intro x _
    positivity
  have h_hc_lhs_nonneg : 0 ≤ expect (fun x => noiseOp ρ (noiseOp ρ f) x ^ 4) := by
    unfold expect uniformWeight
    apply mul_nonneg (by positivity)
    apply Finset.sum_nonneg
    intro x _
    positivity

  have main_bound : E_2 ≤ (expect (fun x => |f x| ^ (4/3 : ℝ))) ^ (3/4 : ℝ) * E_2 ^ (1/2 : ℝ) := by
    calc
      E_2 = innerProduct (noiseOp ρ f) (noiseOp ρ f) := h_inner_eq.symm
      _ = innerProduct f (noiseOp ρ (noiseOp ρ f)) := by
        rw [noiseOp_self_adjoint]
      _ ≤ (expect (fun x => |f x| ^ (4/3 : ℝ))) ^ (3/4 : ℝ) * (expect (fun x => |noiseOp ρ (noiseOp ρ f) x| ^ 4)) ^ (1/4 : ℝ) := by
        apply innerProduct_le_L43_L4
      _ = (expect (fun x => |f x| ^ (4/3 : ℝ))) ^ (3/4 : ℝ) * (expect (fun x => noiseOp ρ (noiseOp ρ f) x ^ 4)) ^ (1/4 : ℝ) := by
        rw [h_abs_four]
      _ ≤ (expect (fun x => |f x| ^ (4/3 : ℝ))) ^ (3/4 : ℝ) * (E_2 ^ 2) ^ (1/4 : ℝ) := by
        apply mul_le_mul_of_nonneg_left
        · apply Real.rpow_le_rpow h_hc_lhs_nonneg hc_2_4 (by norm_num)
        · exact Real.rpow_nonneg h_f_L43_nonneg (3 / 4 : ℝ)
      _ = (expect (fun x => |f x| ^ (4/3 : ℝ))) ^ (3/4 : ℝ) * E_2 ^ (1/2 : ℝ) := by
        congr 1
        have h_nat_real : E_2 ^ (2 : ℕ) = E_2 ^ (2 : ℝ) := (Real.rpow_natCast E_2 2).symm
        rw [h_nat_real]
        rw [← Real.rpow_mul hE2_nonneg]
        norm_num

  have h_split : E_2 ^ (1 / 2 : ℝ) * E_2 ^ (1 / 2 : ℝ) = E_2 := by
    rw [← Real.rpow_add hE2_pos]
    norm_num
  have main_bound_split : E_2 ^ (1 / 2 : ℝ) * E_2 ^ (1 / 2 : ℝ) ≤ (expect (fun x => |f x| ^ (4/3 : ℝ))) ^ (3/4 : ℝ) * E_2 ^ (1 / 2 : ℝ) := by
    calc
      E_2 ^ (1 / 2 : ℝ) * E_2 ^ (1 / 2 : ℝ) = E_2 := h_split
      _ ≤ (expect (fun x => |f x| ^ (4/3 : ℝ))) ^ (3/4 : ℝ) * E_2 ^ (1 / 2 : ℝ) := main_bound
  have hE2_half_pos : 0 < E_2 ^ (1 / 2 : ℝ) := Real.rpow_pos_of_pos hE2_pos (1 / 2 : ℝ)
  exact le_of_mul_le_mul_right main_bound_split hE2_half_pos

end BooleanAnalysis.Hypercontractivity
