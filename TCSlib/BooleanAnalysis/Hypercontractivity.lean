import TCSlib.BooleanAnalysis.Basic
import TCSlib.BooleanAnalysis.Bonami
import Mathlib.Probability.Moments.Basic
import Mathlib.MeasureTheory.MeasurableSpace.Basic
import Mathlib.MeasureTheory.Integral.Lebesgue.Markov
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Probability.ProbabilityMassFunction.Basic
import Mathlib.Probability.ProbabilityMassFunction.Constructions
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.MeasureTheory.Integral.MeanInequalities
import Mathlib.Probability.Distributions.Uniform
import Mathlib.Analysis.MeanInequalities

namespace Hypercontractivity
open BooleanAnalysis

section
open MeasureTheory Set Filter BooleanAnalysis Real Bonami

/-! ## (2,4)-Hypercontractivity Theorem -/
/-
Fourier coefficient of avgLast:
  `(avgLast f)^(S) = f̂(S.image castSucc)`.
-/
lemma fourierCoeff_avgLast {n : ℕ} (f : BooleanFunc (n + 1)) (S : Finset (Fin n)) :
    fourierCoeff (avgLast f) S = fourierCoeff f (S.image Fin.castSucc) := by
  unfold avgLast; simp +decide only [fourierCoeff] ; ring_nf;
  unfold innerProduct; simp +decide only [one_div, mul_comm] ; ring_nf;
  unfold expect; simp +decide only [chiS, restrictLast, one_div, mul_comm, Finset.sum_add_distrib,
    Fin.castSucc_inj, implies_true, injOn_of_eq_iff_eq, Finset.prod_image, Finset.mul_sum _ _ _,
    mul_left_comm] ; ring_nf;
  rw [ add_comm 1 n, uniformWeight_succ ] ; rw [ ← mul_add ] ; rw [ sum_boolCube_succ ] ; ring_nf;
  simp +decide [mul_comm, mul_left_comm, Finset.mul_sum _ _ _]

/-
Fourier coefficient of diffLast:
  `(diffLast f)^(S) = f̂(S.image castSucc ∪ {last n})`.
-/
lemma fourierCoeff_diffLast {n : ℕ} (f : BooleanFunc (n + 1)) (S : Finset (Fin n)) :
    fourierCoeff (diffLast f) S = fourierCoeff f (S.image Fin.castSucc ∪ {Fin.last n}) := by
  -- By definition of `diffLast`, we have that `diffLast f(x) = (f(snoc x false) - f(snoc x true)) / 2`.
  unfold diffLast fourierCoeff innerProduct expect chiS restrictLast
  rw [ uniformWeight_succ ];
  rw [ show ( Finset.univ : Finset ( Fin ( n + 1 ) → Bool ) ) = Finset.image ( fun x : Fin n → Bool => Fin.snoc x Bool.false ) Finset.univ ∪ Finset.image ( fun x : Fin n → Bool => Fin.snoc x Bool.true ) Finset.univ from ?_, Finset.sum_union ];
  · rw [ Finset.sum_image, Finset.sum_image ] <;> norm_num [ Finset.prod_union, Finset.prod_image ] ; ring_nf;
    · simp +decide only [mul_assoc, Finset.sum_add_distrib, Finset.sum_mul _ _ _];
      rw [ mul_add ];
  · norm_num [ Finset.disjoint_left ];
  · ext x;
    by_cases hx : x ( Fin.last n ) <;> simp +decide only [Finset.mem_univ, Finset.mem_union,
      Finset.mem_image, true_and, true_iff];
    · exact Or.inr ⟨ fun i => x i.castSucc, by ext i; cases i using Fin.lastCases <;> aesop ⟩;
    · exact Or.inl ⟨ fun i => x i.castSucc, by ext i; cases i using Fin.lastCases <;> aesop ⟩

/-
`χ_{S.image castSucc}(Fin.snoc x b) = χ_S(x)`: the character of a "lifted" set
  ignores the last coordinate.
-/
lemma chiS_snoc_castSucc {n : ℕ} (S : Finset (Fin n)) (x : BoolCube n) (b : Bool) :
    chiS (S.image Fin.castSucc) (Fin.snoc x b) = chiS S x := by
  unfold chiS; simp_all only [Fin.castSucc_inj, implies_true, injOn_of_eq_iff_eq, Finset.prod_image, Fin.snoc_castSucc];

/-
`χ_{S.image castSucc ∪ {last n}}(Fin.snoc x b) = boolToSign b * χ_S(x)`.
-/
lemma chiS_snoc_with_last {n : ℕ} (S : Finset (Fin n)) (x : BoolCube n) (b : Bool) :
    chiS (S.image Fin.castSucc ∪ {Fin.last n}) (Fin.snoc x b) = boolToSign b * chiS S x := by
  unfold chiS; simp +decide only [Finset.union_singleton, Finset.mem_image, Fin.castSucc_ne_last,
    and_false, exists_false, not_false_eq_true, Finset.prod_insert, Fin.snoc_last, Fin.castSucc_inj,
    implies_true, injOn_of_eq_iff_eq, Finset.prod_image, Fin.snoc_castSucc] ;

/-
Partition of `∑ S : Finset (Fin (n+1))` by membership of `Fin.last n`:
  every subset of `[n+1]` either avoids or contains the last element.
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

/-- Cardinality of a lifted set: `|S.image castSucc| = |S|`. -/
lemma card_image_castSucc {n : ℕ} (S : Finset (Fin n)) :
    (S.image Fin.castSucc).card = S.card := by
  exact Finset.card_image_of_injective S (Fin.castSucc_injective n)

/-
Cardinality: `|S.image castSucc ∪ {last n}| = |S| + 1`.
-/
lemma card_image_castSucc_union_last {n : ℕ} (S : Finset (Fin n)) :
    (S.image Fin.castSucc ∪ {Fin.last n}).card = S.card + 1 := by
  rw [ Finset.card_union, Finset.card_image_of_injective ] <;> norm_num [ Function.Injective ]

/-
The noise operator decomposes along the last coordinate:
  `T_ρ f(snoc x b) = T_ρ(avgLast f)(x) + boolToSign(b) · ρ · T_ρ(diffLast f)(x)`.
-/
lemma noiseOp_snoc {n : ℕ} (ρ : ℝ) (f : BooleanFunc (n + 1)) (x : BoolCube n) (b : Bool) :
    noiseOp ρ f (Fin.snoc x b) =
    noiseOp ρ (avgLast f) x + boolToSign b * ρ * noiseOp ρ (diffLast f) x := by
  convert finset_fin_succ_sum_partition ( fun S ↦ ρ ^ S.card * fourierCoeff f S * chiS S ( Fin.snoc x b ) ) using 1;
  congr! 1;
  · refine' Finset.sum_congr rfl fun T _ => _;
    rw [ ← fourierCoeff_avgLast ];
    rw [ card_image_castSucc, chiS_snoc_castSucc ];
  · rw [ show noiseOp ρ ( diffLast f ) x = ∑ T : Finset ( Fin n ), ρ ^ T.card * fourierCoeff ( diffLast f ) T * chiS T x from rfl ];
    rw [ Finset.mul_sum _ _ _ ] ; refine' Finset.sum_congr rfl fun T hT => _ ; rw [ fourierCoeff_diffLast ] ; rw [ card_image_castSucc_union_last ] ; ring_nf;
    rw [ chiS_snoc_with_last ] ; ring

/-
Fourth moment decomposition with the noise operator.
-/
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

/-
Helper: C² ≤ a²b² and C ≥ 0 implies C ≤ ab (for a,b ≥ 0).
-/
lemma sq_le_sq_mul_of_nonneg {C a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b)
    (h : C ^ 2 ≤ a ^ 2 * b ^ 2) : C ≤ a * b := by
  nlinarith [ mul_nonneg ha hb ]

/-
Helper: a² + 6ρ²ab + ρ⁴b² ≤ (a+b)² when ρ² ≤ 1/3 and a,b ≥ 0.
-/
lemma hypercontractivity_algebra_simple {a b ρ : ℝ}
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hρ : ρ ^ 2 ≤ 1 / 3) :
    a ^ 2 + 6 * ρ ^ 2 * (a * b) + ρ ^ 4 * b ^ 2 ≤ (a + b) ^ 2 := by
  nlinarith [ sq_nonneg ( a - b ), mul_nonneg ha hb, mul_le_mul_of_nonneg_left hρ ( sq_nonneg a ), mul_le_mul_of_nonneg_left hρ ( sq_nonneg b ) ]

/-- Key algebraic inequality: under `ρ² ≤ 1/3`, the recurrence closes. -/
lemma hypercontractivity_algebra' {a b A B C ρ : ℝ}
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hA_nn : 0 ≤ A) (hB_nn : 0 ≤ B) (hC : 0 ≤ C)
    (hA_bound : A ≤ a ^ 2) (hB_bound : B ≤ b ^ 2)
    (hC_bound : C ^ 2 ≤ A * B) (hρ : ρ ^ 2 ≤ 1 / 3) :
    A + 6 * ρ ^ 2 * C + ρ ^ 4 * B ≤ (a + b) ^ 2 := by
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
-/
theorem hypercontractivity_2_4 {n : ℕ} (ρ : ℝ) (hρ : ρ ^ 2 ≤ 1 / 3) (f : BooleanFunc n) :
    expect (fun x => (noiseOp ρ f x) ^ 4) ≤ (expect (fun x => f x ^ 2)) ^ 2 := by
  induction n with
  | zero =>
  unfold expect;
  unfold uniformWeight; norm_num;
  unfold noiseOp; ring_nf;
  erw [ Finset.sum_eq_single ∅ ] <;> norm_num;
  · unfold fourierCoeff;
    unfold innerProduct expect; norm_num [ Fin.eq_zero ] ;
    unfold uniformWeight; norm_num;
  · exact fun h => False.elim <| h rfl;
  · exact fun h => False.elim <| h rfl
  | succ n ih =>
    rw [fourth_moment_noise_decomp, second_moment_decomp]
    exact hypercontractivity_algebra'
      (expect_sq_nonneg (avgLast f))
      (expect_sq_nonneg (diffLast f))
      (expect_fourth_nonneg (noiseOp ρ (avgLast f)))
      (expect_fourth_nonneg (noiseOp ρ (diffLast f)))
      (expect_sq_nonneg_prod (noiseOp ρ (avgLast f)) (noiseOp ρ (diffLast f)))
      (ih (avgLast f))
      (ih (diffLast f))
      (expect_cs_sq (noiseOp ρ (avgLast f)) (noiseOp ρ (diffLast f)))
      hρ

/- **The (4 / 3, 2)-Hypercontractivity Theorem** :-/

/-- Hölder's inequality for p = 4/3 and q = 4. -/
lemma innerProduct_le_L43_L4 (f g : BooleanFunc n) :
  innerProduct f g ≤
  (expect (fun x => |f x| ^ (4/3 : ℝ))) ^ (3/4 : ℝ) *
  (expect (fun x => |g x| ^ 4)) ^ (1/4 : ℝ) := by
    -- Step 1: Expand definitions
  unfold innerProduct expect uniformWeight

  -- Step 2: Push the absolute value inside to bound the sum
  -- f * g ≤ |f * g| = |f| * |g|
  have h_abs : ∑ x : BoolCube n, f x * g x ≤ ∑ x : BoolCube n, |f x| * |g x| := by
    apply Finset.sum_le_sum
    intro x _
    calc
      f x * g x ≤ |f x * g x| := le_abs_self _
      _ = |f x| * |g x| := abs_mul _ _

  -- Step 3: Multiply by the uniform weight (2⁻ⁿ)
  have h_weight_abs :
      (2⁻¹ : ℝ) ^ n * ∑ x : BoolCube n, f x * g x ≤
      (2⁻¹ : ℝ) ^ n * ∑ x : BoolCube n, |f x| * |g x| := by
    apply mul_le_mul_of_nonneg_left h_abs
    positivity

  -- Step 4: Setup conjugate exponents for Hölder's inequality
  let p : ℝ := 4/3
  let q : ℝ := 4
  have hpq : HolderConjugate p q := by
    constructor
    · norm_num -- Proves 1 < p (since 4/3 > 1)
    · norm_num
    · norm_num
  -- Step 5: Apply Hölder's Inequality for sums
  -- Mathlib has theorems like `Real.inner_le_Lp_Lq_of_nonneg` or `Real.sum_mul_le_rpow_mul_rpow`
  -- We will bound the sum of |f| * |g|.
  have holder_sum : ∑ x : BoolCube n, |f x| * |g x| ≤
      (∑ x, |f x| ^ p) ^ (1/p) * (∑ x, |g x| ^ q) ^ (1/q) := by
    -- You may need to adapt this exact lemma name depending on your Mathlib version.
    -- If using NNReal, you would map `|f x|` to NNReal first.
    refine inner_le_Lp_mul_Lq_of_nonneg Finset.univ hpq ?_ ?_
    · exact fun i a => abs_nonneg (f i)
    · exact fun i a => abs_nonneg (g i)

  -- Step 6: Distribute the uniform weight into the powers
  have weight_split : (2⁻¹ : ℝ) ^ n = ((2⁻¹ : ℝ) ^ n) ^ (1/p) * ((2⁻¹ : ℝ) ^ n) ^ (1/q) := by
    have hpq_sum : (1/p : ℝ) + (1/q : ℝ) = 1 := by norm_num
    rw [← Real.rpow_add (by positivity), hpq_sum, Real.rpow_one]

  -- Now string it all together
  calc
    (2⁻¹ : ℝ) ^ n * ∑ x, f x * g x
      ≤ (2⁻¹ : ℝ) ^ n * ∑ x, |f x| * |g x| := h_weight_abs
    _ ≤ (2⁻¹ : ℝ) ^ n * ((∑ x, |f x| ^ p) ^ (1/p) * (∑ x, |g x| ^ q) ^ (1/q)) := by
      apply mul_le_mul_of_nonneg_left holder_sum (by positivity)
    _ = (((2⁻¹ : ℝ) ^ n) ^ (1/p) * (∑ x, |f x| ^ p) ^ (1/p)) * (((2⁻¹ : ℝ) ^ n) ^ (1/q) * (∑ x, |g x| ^ q) ^ (1/q)) := by
      -- Use nth_rw to ONLY rewrite the very first instance of 2⁻¹ ^ n
      calc
        (2⁻¹ : ℝ) ^ n * ((∑ x, |f x| ^ p) ^ (1/p) * (∑ x, |g x| ^ q) ^ (1/q))
          = (((2⁻¹ : ℝ) ^ n) ^ (1/p) * ((2⁻¹ : ℝ) ^ n) ^ (1/q)) * ((∑ x, |f x| ^ p) ^ (1/p) * (∑ x, |g x| ^ q) ^ (1/q)) := by nth_rw 1 [weight_split]
        _ = (((2⁻¹ : ℝ) ^ n) ^ (1/p) * (∑ x, |f x| ^ p) ^ (1/p)) * (((2⁻¹ : ℝ) ^ n) ^ (1/q) * (∑ x, |g x| ^ q) ^ (1/q)) := by ring
        _ = (((2⁻¹ : ℝ) ^ n) ^ (1/p) * (∑ x, |f x| ^ p) ^ (1/p)) * (((2⁻¹ : ℝ) ^ n) ^ (1/q) * (∑ x, |g x| ^ q) ^ (1/q)) := by ring
    _ = ((2⁻¹ : ℝ) ^ n * ∑ x, |f x| ^ p) ^ (1/p) * ((2⁻¹ : ℝ) ^ n * ∑ x, |g x| ^ q) ^ (1/q) := by
      -- Real.mul_rpow requires proofs that the inner sums are non-negative
      have hfp : 0 ≤ ∑ x : BoolCube n, |f x| ^ p := Finset.sum_nonneg (fun x _ => by positivity)
      have hgq : 0 ≤ ∑ x : BoolCube n, |g x| ^ q := Finset.sum_nonneg (fun x _ => by positivity)
      rw [← Real.mul_rpow (by positivity) hfp]
      rw [← Real.mul_rpow (by positivity) hgq]
    _ = (2⁻¹ ^ n * ∑ x, (fun x => |f x| ^ (4 / 3 : ℝ)) x) ^ (3 / 4 : ℝ) * (2⁻¹ ^ n * ∑ x, (fun x => |g x| ^ 4) x) ^ (1 / 4 : ℝ) := by
     -- 1. Prove the outer fraction arithmetic
      have hp_exp : (1 / p : ℝ) = 3 / 4 := by norm_num
      have hq_exp : (1 / q : ℝ) = 1 / 4 := by norm_num
      rw [hp_exp, hq_exp]
      -- 2. Fix the invisible rpow vs npow mismatch for q = 4
      have hq_pow : ∀ x, |g x| ^ q = |g x| ^ 4 := by
        intro x
        -- Reveal that q is (4 : ℝ) and the target is (4 : ℕ)
        change |g x| ^ (4 : ℝ) = |g x| ^ (4 : ℕ)
        -- Apply the Mathlib lemma that links Real powers to Nat powers
        exact Real.rpow_natCast (|g x|) 4
      -- 3. Rewrite the power inside the sum
      simp_rw [hq_pow]
      -- 4. Now rfl perfectly matches everything structurally!
      rfl

theorem hypercontractivity_4_div_3_2 {n : ℕ} (f : BooleanFunc n) :
    (expect (fun x => (noiseOp (1 / Real.sqrt 3) f x) ^ 2)) ^ (1/2 : ℝ)
    ≤ (expect (fun x => |f x| ^ (4/3 : ℝ))) ^ (3/4 : ℝ) := by

  -- 1. Setup the constant ρ
  set ρ := 1 / Real.sqrt 3
  have hρ : ρ ^ 2 ≤ 1 / 3 := by
    dsimp [ρ]
    rw [one_div, inv_pow, Real.sq_sqrt (by positivity)]
    simp only [one_div, le_refl]

  -- 2. Define E_2 as the squared L2 norm for cleaner reading
  set E_2 := expect (fun x => (noiseOp ρ f x) ^ 2)
  have hE2_nonneg : 0 ≤ E_2 := by
    unfold E_2 expect uniformWeight
    apply mul_nonneg (by positivity)
    apply Finset.sum_nonneg
    intro x _
    positivity

  -- 3. Handle the trivial case where T_ρ f is 0 to avoid dividing by zero later
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

  -- 4. Establish that E_2 is strictly positive for division later
  have hE2_pos : 0 < E_2 := lt_of_le_of_ne hE2_nonneg (Ne.symm h_zero)

  -- 5. Helper lemmas for the calc block
  have h_inner_eq : innerProduct (noiseOp ρ f) (noiseOp ρ f) = E_2 := by
    unfold innerProduct E_2 expect
    simp_rw [sq]

  have h_abs_four : expect (fun x => |noiseOp ρ (noiseOp ρ f) x| ^ 4) = expect (fun x => noiseOp ρ (noiseOp ρ f) x ^ 4) := by
    apply congr_arg
    ext x
    -- Prove |y|^4 = y^4 using squares
    calc |noiseOp ρ (noiseOp ρ f) x| ^ 4
      _ = (|noiseOp ρ (noiseOp ρ f) x| ^ 2) ^ 2 := by ring
      _ = (noiseOp ρ (noiseOp ρ f) x ^ 2) ^ 2 := by rw [sq_abs]
      _ = noiseOp ρ (noiseOp ρ f) x ^ 4 := by ring

  -- 6. Bring in the (2,4) hypercontractivity bound
  have hc_2_4 := hypercontractivity_2_4 ρ hρ (noiseOp ρ f)

-- 7. The Core Duality Argument

  -- Helper 1: The L4/3 norm expectation is non-negative
  have h_f_L43_nonneg : 0 ≤ expect (fun x => |f x| ^ (4 / 3 : ℝ)) := by
    unfold expect uniformWeight
    apply mul_nonneg (by positivity)
    apply Finset.sum_nonneg
    intro x _
    positivity

  -- Helper 2: The L4 norm expectation of the noiseOp is non-negative
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
        -- Use our explicit proofs instead of relying on `by positivity`
        apply mul_le_mul_of_nonneg_left
        · apply Real.rpow_le_rpow h_hc_lhs_nonneg hc_2_4 (by norm_num)
        · exact Real.rpow_nonneg h_f_L43_nonneg (3 / 4 : ℝ)
      _ = (expect (fun x => |f x| ^ (4/3 : ℝ))) ^ (3/4 : ℝ) * E_2 ^ (1/2 : ℝ) := by
        congr 1
        -- Convert the inner Nat power to a Real power
        have h_nat_real : E_2 ^ (2 : ℕ) = E_2 ^ (2 : ℝ) := (Real.rpow_natCast E_2 2).symm
        rw [h_nat_real]
        -- Now both powers are Real, so we can multiply them
        rw [← Real.rpow_mul hE2_nonneg]
        norm_num

-- 8. Extract the final result by dividing out E_2^(1/2)
  -- Prove that E_2^(1/2) * E_2^(1/2) = E_2
  have h_split : E_2 ^ (1 / 2 : ℝ) * E_2 ^ (1 / 2 : ℝ) = E_2 := by
    rw [← Real.rpow_add hE2_pos]
    norm_num

  -- Securely attach the split left side to our main bound without touching the right side
  have main_bound_split : E_2 ^ (1 / 2 : ℝ) * E_2 ^ (1 / 2 : ℝ) ≤ (expect (fun x => |f x| ^ (4/3 : ℝ))) ^ (3/4 : ℝ) * E_2 ^ (1 / 2 : ℝ) := by
    calc
      E_2 ^ (1 / 2 : ℝ) * E_2 ^ (1 / 2 : ℝ) = E_2 := h_split
      _ ≤ (expect (fun x => |f x| ^ (4/3 : ℝ))) ^ (3/4 : ℝ) * E_2 ^ (1 / 2 : ℝ) := main_bound

  -- Since A * C ≤ B * C and C > 0, then A ≤ B
  have hE2_half_pos : 0 < E_2 ^ (1 / 2 : ℝ) := Real.rpow_pos_of_pos hE2_pos (1 / 2 : ℝ)
  exact le_of_mul_le_mul_right main_bound_split hE2_half_pos


/-! ## Contractivity of the noise operator (q = 2 case) -/

/-- The L² norm of `T_ρ f` in Fourier space:
`𝔼[(T_ρ f)²] = ∑_S ρ^{2|S|} f̂(S)²`. -/
lemma noise_l2_fourier (ρ : ℝ) (f : BooleanFunc n) :
    innerProduct (noiseOp ρ f) (noiseOp ρ f) =
    ∑ S : Finset (Fin n), (ρ ^ S.card) ^ 2 * fourierCoeff f S ^ 2 := by
  rw [parseval]
  apply Finset.sum_congr rfl
  intro S _
  rw [noiseOp_fourier]
  ring

/-- **Contractivity**: `𝔼[(T_ρ f)²] ≤ 𝔼[f²]` for `ρ² ≤ 1`.
This is the `q = 2` case of hypercontractivity. -/
theorem contractivity (ρ : ℝ) (hρ : ρ ^ 2 ≤ 1) (f : BooleanFunc n) :
    expect (fun x => (noiseOp ρ f x) ^ 2) ≤ expect (fun x => f x ^ 2) := by
  have lhs : expect (fun x => (noiseOp ρ f x) ^ 2) =
      innerProduct (noiseOp ρ f) (noiseOp ρ f) := by
    simp [innerProduct, sq]
  have rhs : expect (fun x => f x ^ 2) = innerProduct f f := by
    simp [innerProduct, sq]
  rw [lhs, rhs, noise_l2_fourier, parseval]
  apply Finset.sum_le_sum
  intro S _
  have h1 : (ρ ^ S.card) ^ 2 = (ρ ^ 2) ^ S.card := by ring
  rw [h1]
  apply mul_le_of_le_one_left (sq_nonneg _)
  exact pow_le_one₀ (sq_nonneg ρ) hρ

/-! ## Combinatorial inequality -/
/-
**Key combinatorial bound**: `C(2k, 2j) ≤ C(k, j) · (2k - 1)^j`.

This is proved by induction on `j`. The induction step shows
`C(2k, 2j) / C(2k, 2(j-1)) · 1/((2k-1) · C(k,j)/C(k,j-1))` ≤ 1,
which reduces to `(2k - 2j + 1) ≤ (2k - 1)(2j - 1)` for `j ≥ 1`.
-/
lemma binom_coeff_ineq (k : ℕ) (hk : 1 ≤ k) (j : ℕ) (hj : j ≤ k) :
    Nat.choose (2 * k) (2 * j) ≤ Nat.choose k j * (2 * k - 1) ^ j := by
  induction j with
  | zero =>
    norm_num;
  | succ j ih => -- By the induction hypothesis, we have `C(2k, 2j) ≤ C(k, j) · (2k-1)^j`.
    have h_ind : Nat.choose (2 * k) (2 * j + 2) ≤ Nat.choose (2 * k) (2 * j) * ((2 * k - 2 * j) * (2 * k - 2 * j - 1)) / ((2 * j + 2) * (2 * j + 1)) := by
      rw [ Nat.le_div_iff_mul_le ];
      · have := Nat.choose_succ_right_eq ( 2 * k ) ( 2 * j );
        have := Nat.choose_succ_right_eq ( 2 * k ) ( 2 * j + 1 );
        rw [ show 2 * k - 2 * j - 1 = 2 * k - ( 2 * j + 1 ) by omega ];
        nlinarith [ Nat.sub_add_cancel ( by linarith : 2 * j ≤ 2 * k ), Nat.sub_add_cancel ( by linarith : 2 * j + 1 ≤ 2 * k ) ];
      · positivity;
    have h_ind_step : Nat.choose (2 * k) (2 * j) * ((2 * k - 2 * j) * (2 * k - 2 * j - 1)) ≤ Nat.choose k j * (2 * k - 1) ^ j * (k - j) * (2 * k - 1) * (2 * j + 2) := by
      have h_ind_step : (2 * k - 2 * j) * (2 * k - 2 * j - 1) ≤ (k - j) * (2 * k - 1) * (2 * j + 2) := by
        zify [ ← mul_tsub ];
        repeat rw [ Nat.cast_sub ] <;> push_cast <;> repeat linarith;
        · nlinarith [ sq ( k - j : ℤ ), sq ( j : ℤ ) ];
        · omega;
      simpa only [ mul_assoc ] using Nat.mul_le_mul ( ih ( Nat.le_of_succ_le hj ) ) h_ind_step;
    have h_final : Nat.choose k j * (k - j) * (2 * k - 1) * (2 * j + 2) ≤ Nat.choose k (j + 1) * (2 * k - 1) * (2 * j + 2) * (2 * j + 1) := by
      have h_final : Nat.choose k j * (k - j) ≤ Nat.choose k (j + 1) * (2 * j + 1) := by
        rw [← Nat.choose_succ_right_eq k j]
        apply Nat.mul_le_mul_left
        omega
      nlinarith only [ h_final, show 0 ≤ ( 2 * k - 1 ) * ( 2 * j + 2 ) by positivity ];
    refine le_trans h_ind ?_;
    refine Nat.div_le_of_le_mul ?_;
    refine le_trans h_ind_step ?_;
    convert Nat.mul_le_mul_right ( ( 2 * k - 1 ) ^ j ) h_final using 1 <;> ring

/-! ## Two-point inequality for even powers -/

/-
**Two-point inequality**: for `ρ² ≤ 1/(2k − 1)`:
`(α + ρβ)^{2k} + (α − ρβ)^{2k} ≤ 2 · (α² + β²)^k`.

The proof compares the binomial expansions term by term, using `binom_coeff_ineq`.
-/
lemma two_point_ineq (k : ℕ) (hk : 1 ≤ k)
    (α β ρ : ℝ) (hρ : ρ ^ 2 ≤ 1 / ((2 : ℝ) * k - 1)) :
    (α + ρ * β) ^ (2 * k) + (α - ρ * β) ^ (2 * k) ≤
    2 * (α ^ 2 + β ^ 2) ^ k := by
  -- By the binomial theorem, we expand both sides.
  have h_expand : (α + ρ * β) ^ (2 * k) + (α - ρ * β) ^ (2 * k) = 2 * ∑ j ∈ Finset.range (k + 1), Nat.choose (2 * k) (2 * j) * α ^ (2 * k - 2 * j) * (ρ ^ 2 * β ^ 2) ^ j := by
    have h_expand : (α + ρ * β) ^ (2 * k) + (α - ρ * β) ^ (2 * k) = ∑ j ∈ Finset.range (2 * k + 1), Nat.choose (2 * k) j * α ^ (2 * k - j) * (ρ * β) ^ j + ∑ j ∈ Finset.range (2 * k + 1), Nat.choose (2 * k) j * α ^ (2 * k - j) * (-ρ * β) ^ j := by
      exact congrArg₂ ( · + · ) ( by rw [ add_comm, add_pow ] ; congr; ext; ring ) ( by rw [ sub_eq_add_neg, add_comm, add_pow ] ; congr; ext; ring );
    -- Combine like terms in the binomial expansion.
    have h_combine : ∑ j ∈ Finset.range (2 * k + 1), Nat.choose (2 * k) j * α ^ (2 * k - j) * (ρ * β) ^ j + ∑ j ∈ Finset.range (2 * k + 1), Nat.choose (2 * k) j * α ^ (2 * k - j) * (-ρ * β) ^ j = ∑ j ∈ Finset.filter (fun j => j % 2 = 0) (Finset.range (2 * k + 1)), Nat.choose (2 * k) j * α ^ (2 * k - j) * (ρ ^ 2 * β ^ 2) ^ (j / 2) * 2 := by
      rw [ ← Finset.sum_add_distrib ] ; rw [ Finset.sum_filter ] ; refine' Finset.sum_congr rfl fun x hx => _ ; rcases Nat.even_or_odd' x with ⟨ c, rfl | rfl ⟩ <;> norm_num [ pow_add, pow_mul ] ; ring;
    -- Notice that Finset.filter (fun j => j % 2 = 0) (Finset.range (2 * k + 1)) is equivalent to Finset.image (fun j => 2 * j) (Finset.range (k + 1)).
    have h_filter : Finset.filter (fun j => j % 2 = 0) (Finset.range (2 * k + 1)) = Finset.image (fun j => 2 * j) (Finset.range (k + 1)) := by
      ext j
      simp [Finset.mem_filter, Finset.mem_image];
      exact ⟨ fun h => ⟨ j / 2, by linarith [ Nat.mod_add_div j 2 ], by linarith [ Nat.mod_add_div j 2 ] ⟩, by rintro ⟨ a, ha, rfl ⟩ ; exact ⟨ by linarith, by norm_num ⟩ ⟩;
    simp_all +decide [ mul_assoc, mul_comm, Finset.mul_sum _ _ _ ];
  have h_expand_rhs : (α ^ 2 + β ^ 2) ^ k = ∑ j ∈ Finset.range (k + 1), Nat.choose k j * α ^ (2 * k - 2 * j) * β ^ (2 * j) := by
    rw [ add_comm, add_pow ] ; congr ; ext ; ring_nf;
    rw [ tsub_mul ];
  -- Apply the inequality term by term to the sums.
  have h_term_by_term : ∀ j ∈ Finset.range (k + 1), Nat.choose (2 * k) (2 * j) * (ρ ^ 2) ^ j ≤ Nat.choose k j := by
    intros j hj
    have h_term : Nat.choose (2 * k) (2 * j) * (ρ ^ 2) ^ j ≤ Nat.choose k j * (2 * k - 1) ^ j * (ρ ^ 2) ^ j := by
      have h_term : Nat.choose (2 * k) (2 * j) ≤ Nat.choose k j * (2 * k - 1) ^ j := by
        convert binom_coeff_ineq k hk j ( Finset.mem_range_succ_iff.mp hj ) using 1;
      exact mul_le_mul_of_nonneg_right ( by rw [ ← @Nat.cast_le ℝ ] at *; cases k <;> norm_num at * ; linarith ) ( by positivity );
    refine le_trans h_term ?_;
    rw [ mul_assoc ];
    exact mul_le_of_le_one_right ( Nat.cast_nonneg _ ) ( by rw [ ← mul_pow ] ; exact pow_le_one₀ ( by exact mul_nonneg ( sub_nonneg_of_le ( by norm_cast; linarith ) ) ( sq_nonneg _ ) ) ( by rw [ le_div_iff₀ ] at * <;> nlinarith [ show ( k : ℝ ) ≥ 1 by norm_cast ] ) );
  rw [ h_expand, h_expand_rhs ];
  refine' mul_le_mul_of_nonneg_left ( Finset.sum_le_sum fun j hj => _ ) zero_le_two;
  convert mul_le_mul_of_nonneg_right ( mul_le_mul_of_nonneg_right ( h_term_by_term j hj ) ( show 0 ≤ α ^ ( 2 * k - 2 * j ) by rw [ show α ^ ( 2 * k - 2 * j ) = ( α ^ 2 ) ^ ( k - j ) by rw [ ← pow_mul, Nat.mul_sub_left_distrib ] ] ; positivity ) ) ( show 0 ≤ β ^ ( 2 * j ) by rw [ pow_mul ] ; positivity ) using 1 ; ring

/-- Two-point inequality, averaged form (dividing by 2). -/
lemma two_point_ineq_avg (k : ℕ) (hk : 1 ≤ k)
    (α β ρ : ℝ) (hρ : ρ ^ 2 ≤ 1 / ((2 : ℝ) * k - 1)) :
    ((α + ρ * β) ^ (2 * k) + (α - ρ * β) ^ (2 * k)) / 2 ≤
    (α ^ 2 + β ^ 2) ^ k := by
  have h := two_point_ineq k hk α β ρ hρ
  linarith

/-! ## Moment decomposition for even powers -/

/-- For even q, the q-th moment decomposes using avgLast and diffLast. -/
lemma qth_moment_decomp (q : ℕ) (f : BooleanFunc (n + 1)) :
    expect (fun x => f x ^ q) =
    expect (fun x' => ((avgLast f x' + diffLast f x') ^ q +
                       (avgLast f x' - diffLast f x') ^ q) / 2) := by
  unfold expect; rw [uniformWeight_succ];
  rw [show (∑ x : BoolCube (n + 1), f x ^ q) = ∑ x : BoolCube n, f (Fin.snoc x Bool.false) ^ q + ∑ x : BoolCube n, f (Fin.snoc x Bool.true) ^ q from ?_];
  · unfold avgLast diffLast; norm_num [Finset.sum_add_distrib, Finset.mul_sum _ _ _, Finset.sum_div]; ring_nf;
    norm_num [Finset.sum_add_distrib, Finset.mul_sum _ _ _, Finset.sum_mul]; ring_nf; rfl;
  · exact sum_boolCube_succ fun x => f x ^ q

/-- The noise operator decomposes on (n+1)-cubes for q-th moments. -/
lemma noise_qth_moment_decomp (q : ℕ) (ρ : ℝ) (f : BooleanFunc (n + 1)) :
    expect (fun x => (noiseOp ρ f x) ^ q) =
    expect (fun x' => ((noiseOp ρ (avgLast f) x' + ρ * noiseOp ρ (diffLast f) x') ^ q +
                       (noiseOp ρ (avgLast f) x' - ρ * noiseOp ρ (diffLast f) x') ^ q) / 2) := by
  convert (qth_moment_decomp q (noiseOp ρ f)) using 3;
  rw [show avgLast (noiseOp ρ f) = noiseOp ρ (avgLast f) from ?_,
      show diffLast (noiseOp ρ f) = ρ • noiseOp ρ (diffLast f) from ?_]; ring_nf!;
  · norm_num [Algebra.smul_def];
  · ext x; exact (by
    convert congr_arg (fun y => (y - (noiseOp ρ f (Fin.snoc x true))) / 2)
      (noiseOp_snoc ρ f x false) using 1; norm_num; ring_nf!;
    rw [show noiseOp ρ f (Fin.snoc x true) =
      noiseOp ρ (avgLast f) x + boolToSign true * ρ * noiseOp ρ (diffLast f) x
      from noiseOp_snoc ρ f x true]; norm_num; ring!;);
  · funext x; simp [avgLast, noiseOp]; unfold restrictLast; ring_nf;
    rw [noiseOp_snoc, noiseOp_snoc]; norm_num; ring!;

/-! ## The main (2, 2k)-Hypercontractivity Theorem -/

/-
**The (2, 2k)-Hypercontractivity Theorem** (Bonami–Beckner):

For any Boolean function `f : {0,1}ⁿ → ℝ`, integer `k ≥ 1`,
and noise parameter `ρ` with `ρ² ≤ 1/(2k − 1)`:

`𝔼[(T_ρ f)^{2k}] ≤ (𝔼[f²])^k`.

Equivalently, `‖T_ρ f‖_{2k} ≤ ‖f‖₂`.

The proof is by induction on the dimension `n` of the Boolean cube.

**Induction step** (sketch):
1. Decompose using `noise_qth_moment_decomp` into terms involving `T_ρ(avgLast f)` and
   `T_ρ(diffLast f)`.
2. Apply the `two_point_ineq` pointwise: each summand is bounded by
   `(T_ρg(x')² + T_ρh(x')²)^k`.
3. Expand `(T_ρg² + T_ρh²)^k` via the binomial theorem.
4. Bound each mixed moment `𝔼[T_ρg^{2i} · T_ρh^{2(k−i)}]` using
   generalized Hölder + the induction hypothesis.
5. Reassemble using `binom_coeff_ineq` and `second_moment_decomp`.
-/
theorem hypercontractivity_2_2k (k : ℕ) (hk : 1 ≤ k)
    (ρ : ℝ) (hρ : ρ ^ 2 ≤ 1 / ((2 : ℝ) * k - 1)) (f : BooleanFunc n) :
    expect (fun x => (noiseOp ρ f x) ^ (2 * k)) ≤ (expect (fun x => f x ^ 2)) ^ k := by
  revert f;
  induction n with
  | zero =>
    intro f
    have h_base : expect (fun x => (noiseOp ρ f x) ^ (2 * k)) = (expect (fun x => f x ^ (2 * k))) := by
      convert rfl using 3;
      convert rfl using 2;
      convert walsh_expansion f ‹_› |> Eq.symm using 1;
      exact Finset.sum_congr rfl fun x hx => by rw [ Finset.card_eq_zero.mpr ( Finset.eq_empty_of_forall_notMem fun y hy => by fin_cases y ) ] ; ring;
    simp_all +decide [ pow_mul ];
    unfold expect; norm_num [ Finset.card_univ ] ;
    norm_num [ uniformWeight ];
  | succ n ih =>
    intro f
    have h_decomp : expect (fun x => (noiseOp ρ f x) ^ (2 * k)) = ∑ j ∈ Finset.range (k + 1), Nat.choose (2 * k) (2 * j) * ρ ^ (2 * j) * expect (fun x' => (noiseOp ρ (avgLast f) x') ^ (2 * k - 2 * j) * (noiseOp ρ (diffLast f) x') ^ (2 * j)) := by
      have h_decomp : ∀ x' : BoolCube n, ((noiseOp ρ (avgLast f) x' + ρ * noiseOp ρ (diffLast f) x') ^ (2 * k) + (noiseOp ρ (avgLast f) x' - ρ * noiseOp ρ (diffLast f) x') ^ (2 * k)) / 2 = ∑ j ∈ Finset.range (k + 1), Nat.choose (2 * k) (2 * j) * ρ ^ (2 * j) * (noiseOp ρ (avgLast f) x') ^ (2 * k - 2 * j) * (noiseOp ρ (diffLast f) x') ^ (2 * j) := by
        intro x'
        have h_expand : ((noiseOp ρ (avgLast f) x' + ρ * noiseOp ρ (diffLast f) x') ^ (2 * k) + (noiseOp ρ (avgLast f) x' - ρ * noiseOp ρ (diffLast f) x') ^ (2 * k)) = ∑ j ∈ Finset.range (2 * k + 1), Nat.choose (2 * k) j * ρ ^ j * (noiseOp ρ (avgLast f) x') ^ (2 * k - j) * (noiseOp ρ (diffLast f) x') ^ j * (if j % 2 = 0 then 2 else 0) := by
          have h_expand : ((noiseOp ρ (avgLast f) x' + ρ * noiseOp ρ (diffLast f) x') ^ (2 * k) + (noiseOp ρ (avgLast f) x' - ρ * noiseOp ρ (diffLast f) x') ^ (2 * k)) = ∑ j ∈ Finset.range (2 * k + 1), Nat.choose (2 * k) j * ρ ^ j * (noiseOp ρ (avgLast f) x') ^ (2 * k - j) * (noiseOp ρ (diffLast f) x') ^ j + ∑ j ∈ Finset.range (2 * k + 1), Nat.choose (2 * k) j * (-ρ) ^ j * (noiseOp ρ (avgLast f) x') ^ (2 * k - j) * (noiseOp ρ (diffLast f) x') ^ j := by
            congr 1;
            · rw [ add_comm, add_pow ] ; congr ; ext ; ring;
            · rw [ sub_eq_add_neg, add_comm, add_pow ] ; congr ; ext ; ring;
          rw [ h_expand, ← Finset.sum_add_distrib ] ; refine' Finset.sum_congr rfl fun j hj => _ ; rcases Nat.even_or_odd' j with ⟨ c, rfl | rfl ⟩ <;> norm_num [ pow_add, pow_mul ] ; ring;
        rw [ h_expand, div_eq_iff ] <;> norm_num [ Finset.sum_ite ];
        rw [ Finset.sum_mul _ _ _ ];
        rw [ show Finset.filter ( fun x => x % 2 = 0 ) ( Finset.range ( 2 * k + 1 ) ) = Finset.image ( fun x => 2 * x ) ( Finset.range ( k + 1 ) ) from ?_, Finset.sum_image <| by norm_num ];
        ext ( _ | x ) <;> simp +arith +decide [ Nat.add_mod];
        exact ⟨ fun h => ⟨ ( x + 1 ) / 2, by omega, by omega ⟩, fun ⟨ a, ha, ha' ⟩ => ⟨ by omega, by omega ⟩ ⟩;
      rw [ noise_qth_moment_decomp ];
      simp +decide only [expect, h_decomp, mul_assoc, Finset.mul_sum _ _ _];
      exact Finset.sum_comm.trans ( Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring );
    -- By the induction hypothesis, we have:
    have h_ind : ∀ j ∈ Finset.range (k + 1), expect (fun x' => (noiseOp ρ (avgLast f) x') ^ (2 * k - 2 * j) * (noiseOp ρ (diffLast f) x') ^ (2 * j)) ≤ (expect (fun x' => (avgLast f x') ^ 2)) ^ (k - j) * (expect (fun x' => (diffLast f x') ^ 2)) ^ j := by
      intro j hj
      have h_ind_step : expect (fun x' => (noiseOp ρ (avgLast f) x') ^ (2 * k - 2 * j) * (noiseOp ρ (diffLast f) x') ^ (2 * j)) ≤ (expect (fun x' => (noiseOp ρ (avgLast f) x') ^ (2 * k))) ^ ((k - j) / k : ℝ) * (expect (fun x' => (noiseOp ρ (diffLast f) x') ^ (2 * k))) ^ (j / k : ℝ) := by
        have h_ind_step : ∀ (g h : BooleanFunc n), 0 ≤ expect (fun x' => g x' ^ (2 * k)) → 0 ≤ expect (fun x' => h x' ^ (2 * k)) → expect (fun x' => g x' ^ (2 * k - 2 * j) * h x' ^ (2 * j)) ≤ (expect (fun x' => g x' ^ (2 * k))) ^ ((k - j) / k : ℝ) * (expect (fun x' => h x' ^ (2 * k))) ^ (j / k : ℝ) := by
          intros g h hg hh
          have h_holder : ∀ (p q : ℝ), 1 < p → 1 < q → p⁻¹ + q⁻¹ = 1 → ∀ (f g : BoolCube n → ℝ), (∀ x', 0 ≤ f x') → (∀ x', 0 ≤ g x') → (∑ x', f x' * g x') ≤ (∑ x', f x' ^ p) ^ (1 / p : ℝ) * (∑ x', g x' ^ q) ^ (1 / q : ℝ) := by
            intros p q hp hq hpq f g hf hg;
            have := @Real.inner_le_Lp_mul_Lq;
            simpa only [ abs_of_nonneg ( hf _ ), abs_of_nonneg ( hg _ ) ] using this Finset.univ f g ( by constructor <;> ring_nf <;> nlinarith [ inv_pos.2 ( zero_lt_one.trans hp ), inv_pos.2 ( zero_lt_one.trans hq ), mul_inv_cancel₀ ( ne_of_gt ( zero_lt_one.trans hp ) ), mul_inv_cancel₀ ( ne_of_gt ( zero_lt_one.trans hq ) ) ] );
          by_cases hj : j = 0 ∨ j = k;
          · cases hj <;> simp +decide [ *, ne_of_gt ( zero_lt_one.trans_le hk ) ];
          · have h_holder : (∑ x', |g x'| ^ (2 * k - 2 * j) * |h x'| ^ (2 * j)) ≤ (∑ x', |g x'| ^ (2 * k)) ^ ((k - j) / k : ℝ) * (∑ x', |h x'| ^ (2 * k)) ^ (j / k : ℝ) := by
              convert h_holder ( k / ( k - j ) ) ( k / j ) _ _ _ ( fun x' => |g x'| ^ ( 2 * k - 2 * j ) ) ( fun x' => |h x'| ^ ( 2 * j ) ) _ _ using 1 <;> norm_num;
              · congr! 2;
                · refine' Finset.sum_congr rfl fun x' _ => _;
                  rw [ ← Real.rpow_natCast _ ( 2 * k - 2 * j ), ← Real.rpow_mul ( abs_nonneg _ ) ] ; norm_num [ Nat.cast_sub ( show 2 * j ≤ 2 * k from by linarith [ Finset.mem_range.mp ‹_› ] ) ];
                  rw [ show ( 2 * k - 2 * j : ℝ ) * ( k / ( k - j ) ) = 2 * k by rw [ mul_div, div_eq_iff ] <;> nlinarith [ show ( j : ℝ ) < k from mod_cast lt_of_le_of_ne ( Finset.mem_range_succ_iff.mp ‹_› ) ( by tauto ) ] ] ; norm_cast;
                · refine' Finset.sum_congr rfl fun x' _ => _;
                  rw [ ← Real.rpow_natCast _ ( 2 * j ), ← Real.rpow_mul ( abs_nonneg _ ) ] ; ring_nf ; norm_num [ show j ≠ 0 by tauto ];
                  norm_num [ mul_assoc, mul_comm, mul_left_comm, show j ≠ 0 by tauto ];
                  norm_cast;
              · rw [ lt_div_iff₀ ] <;> norm_num;
                · exact Nat.pos_of_ne_zero fun h => hj <| Or.inl h;
                · exact lt_of_le_of_ne ( Finset.mem_range_succ_iff.mp ‹_› ) ( by tauto );
              · rw [ lt_div_iff₀ ] <;> norm_cast <;> cases lt_or_gt_of_ne ( mt Or.inl hj ) <;> cases lt_or_gt_of_ne ( mt Or.inr hj ) <;> linarith [ Finset.mem_range.mp ‹_› ];
              · rw [ ← add_div, div_eq_iff ] <;> norm_num ; linarith;
            convert mul_le_mul_of_nonneg_left h_holder ( show 0 ≤ uniformWeight n by exact pow_nonneg ( by norm_num ) _ ) using 1 <;> norm_num [ expect ];
            · norm_num [ pow_mul ];
              exact Or.inl ( Finset.sum_congr rfl fun _ _ => by rw [ abs_eq_max_neg, max_def ] ; split_ifs <;> simp +decide [ *, Nat.even_sub ( show 2 * j ≤ 2 * k from by linarith [ Finset.mem_range.mp ‹_› ] ) ] );
            · norm_num [ pow_mul, abs_mul, abs_pow ];
              rw [ Real.mul_rpow ( by exact pow_nonneg ( by norm_num ) _ ) ( Finset.sum_nonneg fun _ _ => by positivity ), Real.mul_rpow ( by exact pow_nonneg ( by norm_num ) _ ) ( Finset.sum_nonneg fun _ _ => by positivity ) ] ; ring_nf;
              norm_num [ mul_assoc, mul_comm, mul_left_comm, ne_of_gt ( zero_lt_one.trans_le hk ) ];
              rw [ ← mul_assoc, ← Real.rpow_add ( by exact pow_pos ( by norm_num ) _ ) ] ; norm_num [ show k ≠ 0 by linarith ];
        apply h_ind_step;
        · exact mul_nonneg ( pow_nonneg ( by norm_num ) _ ) ( Finset.sum_nonneg fun _ _ => pow_mul ( noiseOp ρ ( avgLast f ) _ ) 2 k ▸ by positivity );
        · exact mul_nonneg ( pow_nonneg ( by norm_num ) _ ) ( Finset.sum_nonneg fun _ _ => pow_mul ( noiseOp ρ ( diffLast f ) _ ) 2 k ▸ by positivity );
      refine le_trans h_ind_step ?_;
      gcongr;
      · refine' Real.rpow_nonneg _ _;
        exact mul_nonneg ( pow_nonneg ( by norm_num ) _ ) ( Finset.sum_nonneg fun _ _ => pow_mul ( noiseOp ρ ( diffLast f ) _ ) 2 k ▸ by positivity );
      · exact pow_nonneg (expect_sq_nonneg (avgLast f)) _;
      · refine' le_trans ( Real.rpow_le_rpow ( _ ) ( ih _ ) ( _ ) ) _;
        · exact mul_nonneg ( by exact pow_nonneg ( by norm_num ) _ ) ( Finset.sum_nonneg fun _ _ => pow_mul ( noiseOp ρ ( avgLast f ) _ ) 2 k ▸ by positivity );
        · exact div_nonneg ( sub_nonneg_of_le ( Nat.cast_le.mpr ( Finset.mem_range_succ_iff.mp hj ) ) ) ( Nat.cast_nonneg _ );
        · rw [ ← Real.rpow_natCast, ← Real.rpow_mul ( expect_sq_nonneg _ ), mul_comm ];
          rw [ div_mul_cancel₀ _ ( by positivity ), ← Nat.cast_sub ( Finset.mem_range_succ_iff.mp hj ) ] ; norm_cast;
      · convert Real.rpow_le_rpow ( ?_ ) ( ih ( diffLast f ) ) ( show ( 0 : ℝ ) ≤ j / k by positivity ) using 1;
        · rw [ ← Real.rpow_natCast _ k, ← Real.rpow_mul (expect_sq_nonneg (diffLast f)), mul_div_cancel₀ _ ( by positivity ), Real.rpow_natCast ];
        · exact le_of_not_gt fun h => by have := expect_sq_nonneg ( fun x => noiseOp ρ ( diffLast f ) x ^ k ) ; norm_num [ pow_mul' ] at * ; linarith;
    -- By the binomial coefficient inequality, we have:
    have h_binom : ∀ j ∈ Finset.range (k + 1), Nat.choose (2 * k) (2 * j) * ρ ^ (2 * j) ≤ Nat.choose k j * (ρ ^ 2 * (2 * k - 1)) ^ j := by
      intros j hj
      have h_binom_coeff : Nat.choose (2 * k) (2 * j) ≤ Nat.choose k j * (2 * k - 1) ^ j := by
        apply binom_coeff_ineq k hk j (Finset.mem_range_succ_iff.mp hj);
      convert mul_le_mul_of_nonneg_right ( Nat.cast_le.mpr h_binom_coeff ) ( pow_mul ρ 2 j ▸ by positivity : 0 ≤ ρ ^ ( 2 * j ) ) using 1 ; ring_nf;
      rw [ Nat.cast_mul, Nat.cast_pow, Nat.cast_sub ( by linarith ) ] ; push_cast ; ring_nf;
      rw [ show ( -ρ ^ 2 + ρ ^ 2 * k * 2 : ℝ ) = ρ ^ 2 * ( -1 + k * 2 ) by ring ] ; rw [ mul_pow ] ; ring;
    -- By combining the results from the decomposition, induction hypothesis, and binomial coefficient inequality, we get:
    have h_combined : expect (fun x => (noiseOp ρ f x) ^ (2 * k)) ≤ ∑ j ∈ Finset.range (k + 1), Nat.choose k j * (ρ ^ 2 * (2 * k - 1)) ^ j * (expect (fun x' => (avgLast f x') ^ 2)) ^ (k - j) * (expect (fun x' => (diffLast f x') ^ 2)) ^ j := by
      rw [h_decomp];
      refine Finset.sum_le_sum fun j hj => ?_;
      refine le_trans ( mul_le_mul_of_nonneg_left ( h_ind j hj ) ?_ ) ?_;
      · exact mul_nonneg ( Nat.cast_nonneg _ ) ( pow_mul ρ 2 j ▸ by positivity );
      · simpa only [ mul_assoc ] using mul_le_mul_of_nonneg_right ( h_binom j hj ) ( mul_nonneg ( pow_nonneg ( expect_sq_nonneg _ ) _ ) ( pow_nonneg ( expect_sq_nonneg _ ) _ ) );
    -- By the binomial theorem, we have:
    have h_binom_theorem : ∑ j ∈ Finset.range (k + 1), Nat.choose k j * (ρ ^ 2 * (2 * k - 1)) ^ j * (expect (fun x' => (avgLast f x') ^ 2)) ^ (k - j) * (expect (fun x' => (diffLast f x') ^ 2)) ^ j = (expect (fun x' => (avgLast f x') ^ 2) + ρ ^ 2 * (2 * k - 1) * expect (fun x' => (diffLast f x') ^ 2)) ^ k := by
      rw [ add_comm, add_pow ];
      rw [ add_comm, ← Finset.sum_flip ];
      refine' Finset.sum_congr rfl fun x hx => _;
      rw [ Nat.choose_symm ( Finset.mem_range_succ_iff.mp hx ), tsub_tsub_cancel_of_le ( Finset.mem_range_succ_iff.mp hx ) ] ; ring_nf;
      rw [ show ( -ρ ^ 2 + ρ ^ 2 * k * 2 : ℝ ) = ( ρ ^ 2 * k * 2 - ρ ^ 2 ) by ring ] ; rw [ show ( ρ ^ 2 * k * expect ( fun x' => diffLast f x' ^ 2 ) * 2 - ρ ^ 2 * expect ( fun x' => diffLast f x' ^ 2 ) ) = ( ρ ^ 2 * k * 2 - ρ ^ 2 ) * expect ( fun x' => diffLast f x' ^ 2 ) by ring ] ; rw [ mul_pow ] ; ring;
    refine le_trans h_combined <| h_binom_theorem.le.trans ?_;
    gcongr;
    · exact add_nonneg ( expect_sq_nonneg _ ) ( mul_nonneg ( mul_nonneg ( sq_nonneg _ ) ( sub_nonneg.mpr ( by norm_cast; linarith ) ) ) ( expect_sq_nonneg _ ) );
    · rw [ second_moment_decomp ];
      rw [ le_div_iff₀ ] at hρ <;> nlinarith [ show ( k : ℝ ) ≥ 1 by norm_cast, show ( expect fun x' => diffLast f x' ^ 2 ) ≥ 0 by exact expect_sq_nonneg _ ]

/-! ## Equivalent formulation with q -/

/-- The (2, q)-Hypercontractivity restated with even `q`. -/
theorem hypercontractivity_2_q (q : ℕ) (hq : 2 ≤ q) (hq_even : Even q)
    (ρ : ℝ) (hρ : ρ ^ 2 ≤ 1 / ((q : ℝ) - 1)) (f : BooleanFunc n) :
    expect (fun x => (noiseOp ρ f x) ^ q) ≤ (expect (fun x => f x ^ 2)) ^ (q / 2) := by
  obtain ⟨k, rfl⟩ := hq_even
  have hk : 1 ≤ k := by omega
  simp only [show k + k = 2 * k from by ring, Nat.mul_div_cancel_left _ (by norm_num : 0 < 2)]
  apply hypercontractivity_2_2k k hk ρ _ f
  convert hρ using 1
  push_cast; ring

/-! ## Corollaries and specific cases -/

/-- The (2, 2)-hypercontractivity is just contractivity. -/
theorem hypercontractivity_2_2 (ρ : ℝ) (hρ : ρ ^ 2 ≤ 1) (f : BooleanFunc n) :
    expect (fun x => (noiseOp ρ f x) ^ 2) ≤ (expect (fun x => f x ^ 2)) ^ 1 := by
  rw [pow_one]
  exact contractivity ρ hρ f

/-- The (2, 4)-hypercontractivity instantiation. -/
theorem hypercontractivity_2_4_inst (ρ : ℝ) (hρ : ρ ^ 2 ≤ 1 / 3) (f : BooleanFunc n) :
    expect (fun x => (noiseOp ρ f x) ^ 4) ≤ (expect (fun x => f x ^ 2)) ^ 2 :=
  hypercontractivity_2_4 ρ hρ f

/-- The (2, 6)-hypercontractivity. -/
theorem hypercontractivity_2_6 (ρ : ℝ) (hρ : ρ ^ 2 ≤ 1 / 5) (f : BooleanFunc n) :
    expect (fun x => (noiseOp ρ f x) ^ 6) ≤ (expect (fun x => f x ^ 2)) ^ 3 := by
  exact hypercontractivity_2_q 6 (by norm_num) ⟨3, by ring⟩ ρ (by linarith) f

/-! ## Real-power formulation -/

/-
The (2, 2k)-hypercontractivity in `‖·‖_{2k} ≤ ‖·‖_2` form.
-/
theorem hypercontractivity_2_2k_rpow (k : ℕ) (hk : 1 ≤ k)
    (ρ : ℝ) (hρ : ρ ^ 2 ≤ 1 / ((2 : ℝ) * k - 1)) (f : BooleanFunc n) :
    (expect (fun x => (noiseOp ρ f x) ^ (2 * k))) ^ (1 / (2 * k : ℝ)) ≤
    (expect (fun x => f x ^ 2)) ^ (1 / 2 : ℝ) := by
  convert Real.rpow_le_rpow ( ?_ ) ( hypercontractivity_2_2k k ( by linarith ) ( ρ ) ?_ ( f ) ) ?_ using 1;
  · rw [ ← Real.rpow_natCast, ← Real.rpow_mul ( expect_sq_nonneg _ ) ] ; ring_nf ; norm_num [ show k ≠ 0 by linarith ];
  · convert expect_sq_nonneg ( fun x => noiseOp ρ f x ^ k ) using 1;
    exact congr_arg _ ( funext fun x => by ring );
  · exact hρ;
  · positivity

/-! ## (p, 2)-Hypercontractivity via Duality -/

lemma innerProduct_eq_expect_sq (f : BooleanFunc n) :
    innerProduct f f = BooleanAnalysis.expect (fun x => f x ^ 2) := by
  unfold innerProduct BooleanAnalysis.expect uniformWeight
  congr 1
  apply Finset.sum_congr rfl
  intro x _; ring

lemma expect_sq_noiseOp_nonneg (ρ : ℝ) (f : BooleanFunc n) :
    0 ≤ BooleanAnalysis.expect (fun x => (noiseOp ρ f x) ^ 2) := by
  unfold BooleanAnalysis.expect uniformWeight
  apply mul_nonneg (pow_nonneg (by positivity) _)
  apply Finset.sum_nonneg
  intro x _; positivity

lemma expect_rpow_abs_nonneg (p : ℝ) (f : BooleanFunc n) :
    0 ≤ BooleanAnalysis.expect (fun x => |f x| ^ p) := by
  unfold BooleanAnalysis.expect uniformWeight
  apply mul_nonneg (pow_nonneg (by positivity) _)
  apply Finset.sum_nonneg
  intro x _; positivity

lemma noiseOp_compose (ρ σ : ℝ) (f : BooleanFunc n) :
    noiseOp ρ (noiseOp σ f) = noiseOp (ρ * σ) f := by
  ext x
  simp only [noiseOp]
  congr 1; ext S
  rw [noiseOp_fourier]; ring

/--
**The (p, 2)-Hypercontractivity Theorem** (general duality framework):

Given a (2, q)-hypercontractivity bound and Hölder's inequality for `(p, q)`,
we conclude `(𝔼[(T_ρ f)²])^{1/2} ≤ (𝔼[|f|^p])^{1/p}`.

The proof:
1. `‖T_ρ f‖₂² = ⟨T_ρ f, T_ρ f⟩ = ⟨f, T_ρ(T_ρ f)⟩` by self-adjointness
2. `⟨f, T_ρ(T_ρ f)⟩ ≤ ‖f‖_p · ‖T_ρ(T_ρ f)‖_q` by Hölder
3. `‖T_ρ(T_ρ f)‖_q ≤ ‖T_ρ f‖₂` by (2,q)-hypercontractivity
4. Divide both sides by `‖T_ρ f‖₂`. -/
theorem hypercontractivity_p_2_general
    {ρ : ℝ} {p q : ℝ}
    (hp : 1 < p) (hq : 2 ≤ q)
    (hpq : 1/p + 1/q = 1)
    (f : BooleanFunc n)
    (holder : ∀ (u v : BooleanFunc n),
      innerProduct u v ≤
      (BooleanAnalysis.expect (fun x => |u x| ^ p)) ^ (1/p) *
      (BooleanAnalysis.expect (fun x => |v x| ^ q)) ^ (1/q))
    (hyp_2_q : ∀ (g : BooleanFunc n),
      BooleanAnalysis.expect (fun x => |noiseOp ρ g x| ^ q) ≤
      (BooleanAnalysis.expect (fun x => g x ^ 2)) ^ (q/2)) :
    (BooleanAnalysis.expect (fun x => (noiseOp ρ f x) ^ 2)) ^ (1/2 : ℝ) ≤
    (BooleanAnalysis.expect (fun x => |f x| ^ p)) ^ (1/p) := by
  set E₂ := BooleanAnalysis.expect (fun x => (noiseOp ρ f x) ^ 2)
  have hE₂_nn : 0 ≤ E₂ := expect_sq_noiseOp_nonneg ρ f
  by_cases hE₂_zero : E₂ = 0
  · rw [hE₂_zero]
    simp only [Real.zero_rpow (by norm_num : (1:ℝ)/2 ≠ 0)]
    exact Real.rpow_nonneg (expect_rpow_abs_nonneg p f) _
  have hE₂_pos : 0 < E₂ := lt_of_le_of_ne hE₂_nn (Ne.symm hE₂_zero)
  have h_inner : innerProduct (noiseOp ρ f) (noiseOp ρ f) = E₂ := by
    rw [innerProduct_eq_expect_sq]
  have h_self_adj : E₂ = innerProduct f (noiseOp ρ (noiseOp ρ f)) := by
    rw [← h_inner, noiseOp_self_adjoint]
  have h_holder := holder f (noiseOp ρ (noiseOp ρ f))
  have hq_pos : 0 < q := by linarith
  have h_Lq_bound :
      (BooleanAnalysis.expect (fun x => |noiseOp ρ (noiseOp ρ f) x| ^ q)) ^ (1/q) ≤
      E₂ ^ (1/2 : ℝ) := by
    have step1 : (BooleanAnalysis.expect (fun x => |noiseOp ρ (noiseOp ρ f) x| ^ q)) ^ (1/q) ≤
        ((BooleanAnalysis.expect (fun x => (noiseOp ρ f x) ^ 2)) ^ (q/2)) ^ (1/q) := by
      apply Real.rpow_le_rpow
        (expect_rpow_abs_nonneg q (noiseOp ρ (noiseOp ρ f)))
        (hyp_2_q (noiseOp ρ f))
        (by positivity)
    have step2 : ((BooleanAnalysis.expect (fun x => (noiseOp ρ f x) ^ 2)) ^ (q/2)) ^ (1/q) =
        E₂ ^ (1/2 : ℝ) := by
      rw [← Real.rpow_mul hE₂_nn]
      congr 1; field_simp
    linarith
  have main_bound : E₂ ≤
      (BooleanAnalysis.expect (fun x => |f x| ^ p)) ^ (1/p) * E₂ ^ (1/2 : ℝ) := by
    calc E₂ = innerProduct f (noiseOp ρ (noiseOp ρ f)) := h_self_adj
      _ ≤ (BooleanAnalysis.expect (fun x => |f x| ^ p)) ^ (1/p) *
          (BooleanAnalysis.expect (fun x => |noiseOp ρ (noiseOp ρ f) x| ^ q)) ^ (1/q) :=
        h_holder
      _ ≤ (BooleanAnalysis.expect (fun x => |f x| ^ p)) ^ (1/p) * E₂ ^ (1/2 : ℝ) := by
          apply mul_le_mul_of_nonneg_left h_Lq_bound
          exact Real.rpow_nonneg (expect_rpow_abs_nonneg p f) _
  have h_half_pos : 0 < E₂ ^ (1/2 : ℝ) := Real.rpow_pos_of_pos hE₂_pos _
  have h_split : E₂ ^ (1/2 : ℝ) * E₂ ^ (1/2 : ℝ) = E₂ := by
    rw [← Real.rpow_add hE₂_pos]; norm_num
  have step3 : E₂ ^ (1/2 : ℝ) * E₂ ^ (1/2 : ℝ) ≤
      (BooleanAnalysis.expect (fun x => |f x| ^ p)) ^ (1/p) * E₂ ^ (1/2 : ℝ) := by
    rw [h_split]; exact main_bound
  exact le_of_mul_le_mul_right step3 h_half_pos

/-- (4/3, 2)-hypercontractivity via the existing theorem. -/
theorem hypercontractivity_p_2_at_4_div_3 (f : BooleanFunc n) :
    (BooleanAnalysis.expect (fun x => (noiseOp (1 / Real.sqrt 3) f x) ^ 2)) ^ (1/2 : ℝ) ≤
    (BooleanAnalysis.expect (fun x => |f x| ^ (4/3 : ℝ))) ^ (3/4 : ℝ) :=
  hypercontractivity_4_div_3_2 f

end
end Hypercontractivity
