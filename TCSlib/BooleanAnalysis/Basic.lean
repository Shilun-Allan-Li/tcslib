import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Module.Pi
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Finset.SymmDiff
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Powerset
import Mathlib.Data.Real.Basic
import Mathlib.Data.Real.Sqrt
import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
import Mathlib.Order.BooleanAlgebra.Basic
import Mathlib.Order.SymmDiff
import Mathlib.Probability.Moments.Basic
import TCSlib.BooleanAnalysis.Circuit

/-!
# Boolean Analysis

This file develops the basic theory of Boolean functions `f : {-1, 1}ⁿ → ℝ` (or equivalently
`f : {0, 1}ⁿ → ℝ`) and their Fourier–Walsh expansion over the real numbers.

## Main definitions

* `BooleanFunc n`: the type of functions `(Fin n → Bool) → ℝ`.
* `innerProduct f g`: the inner product `𝔼[f · g] = 2⁻ⁿ ∑_{x} f(x) g(x)`.
* `chiS n S`: the Walsh–Fourier character `χ_S(x) = (-1)^{|S ∩ supp(x)|}` for `S : Finset (Fin n)`.
* `fourierCoeff f S`: the Fourier coefficient `f̂(S) = ⟪f, χ_S⟫`.
* `influence i f`: the influence of coordinate `i` on `f`,
  `Inf_i[f] = 𝔼[(f(x) - f(xⁱ))² / 4]` where `xⁱ` is `x` with bit `i` flipped.
* `totalInfluence f`: the total influence `I[f] = ∑ᵢ Inf_i[f]`.
* `noise f ρ`: the noise operator `T_ρ f(x) = 𝔼_y[f(y)]` where each bit of `y` is `x` independently
  with probability `(1+ρ)/2` and flipped with probability `(1-ρ)/2`.

## Main results

* `walsh_expansion`: every Boolean function has a unique Fourier–Walsh expansion
  `f = ∑_{S ⊆ [n]} f̂(S) χ_S`.
* `parseval`: Parseval's identity `‖f‖² = ∑_S f̂(S)²`.
* `fourier_coeff_chi`: orthonormality of the Walsh characters, `⟪χ_S, χ_T⟫ = [S = T]`.
* `totalInfluence_eq_sum_sq_deg`: `I[f] = ∑_S |S| · f̂(S)²`.

## Notation

* `𝔹 n` for `Fin n → Bool` (the Boolean hypercube).
* `⟪f, g⟫_𝔹` for the Boolean inner product.
* `χ_[S]` for the Walsh character of `S`.

## References

* Ryan O'Donnell, *Analysis of Boolean Functions*, Cambridge University Press, 2014.
-/

set_option maxHeartbeats 400000

open scoped BigOperators

namespace BooleanAnalysis

/-! ## Setup: the Boolean hypercube -/

/-- The Boolean hypercube `{0,1}ⁿ`. -/
abbrev BoolCube (n : ℕ) := Fin n → Bool

/-- A Boolean function `f : {0,1}ⁿ → ℝ`. -/
abbrev BooleanFunc (n : ℕ) := BoolCube n → ℝ

variable {n : ℕ}

/-! ## Uniform measure and expectation -/

/-- The uniform probability measure on `{0,1}ⁿ` assigns weight `2⁻ⁿ` to each point. -/
noncomputable def uniformWeight (n : ℕ) : ℝ := (2 : ℝ)⁻¹ ^ n

/-- Expectation of `f` under the uniform measure on `{0,1}ⁿ`.
  `𝔼[f] = 2⁻ⁿ · ∑_{x ∈ {0,1}ⁿ} f(x)`. -/
noncomputable def expect (f : BooleanFunc n) : ℝ :=
  uniformWeight n * ∑ x : BoolCube n, f x

/-- The `L²` inner product on Boolean functions with respect to the uniform measure:
  `⟪f, g⟫ = 𝔼[f · g] = 2⁻ⁿ · ∑_x f(x) g(x)`. -/
noncomputable def innerProduct (f g : BooleanFunc n) : ℝ :=
  expect (fun x ↦ f x * g x)

scoped notation "⟪" f ", " g "⟫_𝔹" => innerProduct f g

/-- The `L²` norm of a Boolean function: `‖f‖ = √(⟪f, f⟫)`. -/
noncomputable def l2Norm (f : BooleanFunc n) : ℝ :=
  Real.sqrt (innerProduct f f)

/-- The `p`-th moment of a Boolean function under the uniform measure is
  the `p`-th power of the expectation. -/
lemma moment_eq_expect {n : ℕ} (f : BooleanFunc n) (p : ℕ)
    (P : MeasureTheory.Measure (BoolCube n)) [MeasureTheory.IsProbabilityMeasure P]
    (hP_unif : ∀ x, (P {x}).toReal = uniformWeight n) :
    ProbabilityTheory.moment f p P = expect (fun x ↦ f x ^ p) := by
  -- Expand the definition of moment
  rw [ProbabilityTheory.moment]

  -- Convert the discrete integral to a finite sum.
  -- With [IsProbabilityMeasure P] added, integral_fintype now perfectly matches!
  simp only [Pi.pow_apply, MeasureTheory.Integrable.of_finite, MeasureTheory.integral_fintype, smul_eq_mul]

  -- Expand expect and push the constant uniform weight into the sum
  unfold expect
  rw [Finset.mul_sum]

  -- Show the inner terms are exactly equal
  apply Finset.sum_congr rfl
  intro x _
  have h_meas_x : (P.real {x}) = uniformWeight n := hP_unif x

  -- Substitute the uniform weight and rearrange
  rw [h_meas_x]

/-! ## Walsh–Fourier characters -/

/-- Convert a `Bool` to `{-1, 1} ⊆ ℝ`: `false ↦ 1`, `true ↦ -1`. -/
def boolToSign (b : Bool) : ℝ := if b then -1 else 1

@[simp]
lemma boolToSign_false : boolToSign false = 1 := rfl

@[simp]
lemma boolToSign_true : boolToSign true = -1 := rfl

@[simp]
lemma boolToSign_sq (b : Bool) : boolToSign b ^ 2 = 1 := by
  cases b <;> simp [boolToSign]

@[simp]
lemma boolToSign_mul_self (b : Bool) : boolToSign b * boolToSign b = 1 := by
  cases b <;> simp [boolToSign]

/-- The Walsh–Fourier character `χ_S : {0,1}ⁿ → ℝ` associated to a set `S ⊆ [n]`.
  `χ_S(x) = ∏_{i ∈ S} (-1)^{x_i}`.

  This forms an orthonormal basis for `L²({0,1}ⁿ, uniform)`. -/
noncomputable def chiS (S : Finset (Fin n)) : BooleanFunc n :=
  fun x ↦ ∏ i ∈ S, boolToSign (x i)

scoped notation "χ_[" S "]" => chiS S

/-- The character `χ_∅` is the constant function `1`. -/
@[simp]
lemma chiS_empty : χ_[(∅ : Finset (Fin n))] = fun _ ↦ 1 := by
  ext x; simp [chiS]

/-- The character `χ_{i}` for a singleton `{i}` equals `(-1)^{x_i}`. -/
@[simp]
lemma chiS_singleton (i : Fin n) (x : BoolCube n) :
    χ_[{i}] x = boolToSign (x i) := by
  simp [chiS]

/-- Walsh characters take values in `{-1, 1}`. -/
lemma chiS_sq_eq_one (S : Finset (Fin n)) (x : BoolCube n) :
    χ_[S] x ^ 2 = 1 := by
  simp only [chiS]
  induction S using Finset.induction with
  | empty => simp
  | insert a s ha ih =>
    rw [Finset.prod_insert ha, mul_pow, boolToSign_sq, one_mul]
    exact ih

/-- Walsh characters are multiplicative: `χ_{S ∪ T}(x) = χ_S(x) · χ_T(x)` when `S` and `T`
  are disjoint. -/
lemma chiS_mul_of_disjoint (S T : Finset (Fin n)) (hST : Disjoint S T) (x : BoolCube n) :
    χ_[S ∪ T] x = χ_[S] x * χ_[T] x := by
  simp [chiS, Finset.prod_union hST]

/-- The pointwise product of two Walsh characters is another Walsh character (up to sign),
  specifically `χ_S · χ_T = χ_{S Δ T}` where `Δ` denotes symmetric difference. -/
lemma chiS_mul_chiS (S T : Finset (Fin n)) (x : BoolCube n) :
    χ_[S] x * χ_[T] x = χ_[symmDiff S T] x := by
  simp only [chiS]
  -- Decompose: S = (S \ T) ∪ (S ∩ T), T = (T \ S) ∪ (T ∩ S)
  have hS : ∏ i ∈ S, boolToSign (x i) =
      (∏ i ∈ S \ T, boolToSign (x i)) * ∏ i ∈ S ∩ T, boolToSign (x i) := by
    conv_lhs => rw [← Finset.sdiff_union_inter S T]
    apply Finset.prod_union
    simp only [Finset.disjoint_left, Finset.mem_sdiff, Finset.mem_inter, not_and]
    tauto
  have hT : ∏ i ∈ T, boolToSign (x i) =
      (∏ i ∈ T \ S, boolToSign (x i)) * ∏ i ∈ S ∩ T, boolToSign (x i) := by
    conv_lhs => rw [← Finset.sdiff_union_inter T S]
    rw [Finset.inter_comm T S]
    apply Finset.prod_union
    simp only [Finset.disjoint_left, Finset.mem_sdiff, Finset.mem_inter, not_and]
    tauto
  -- The intersection product squares to 1
  have hcancel : (∏ i ∈ S ∩ T, boolToSign (x i)) * ∏ i ∈ S ∩ T, boolToSign (x i) = 1 := by
    rw [← Finset.prod_mul_distrib]; simp [boolToSign_mul_self]
  rw [hS, hT, symmDiff_def, Finset.sup_eq_union, Finset.prod_union disjoint_sdiff_sdiff]
  -- Goal: (A * P) * (B * P) = A * B  where P² = 1
  set P := ∏ i ∈ S ∩ T, boolToSign (x i)
  set A := ∏ i ∈ S \ T, boolToSign (x i)
  set B := ∏ i ∈ T \ S, boolToSign (x i)
  calc A * P * (B * P) = A * B * (P * P) := by ring
    _ = A * B * 1 := by rw [hcancel]
    _ = A * B := by ring

/-! ## Fourier coefficients -/

/-- The Fourier–Walsh coefficient of `f` at frequency `S`:
  `f̂(S) = ⟪f, χ_S⟫ = 2⁻ⁿ · ∑_x f(x) · χ_S(x)`. -/
noncomputable def fourierCoeff (f : BooleanFunc n) (S : Finset (Fin n)) : ℝ :=
  innerProduct f (chiS S)

scoped notation f "̂(" S ")" => fourierCoeff f S

/-- The Fourier coefficient at `∅` equals the expectation of `f`. -/
lemma fourierCoeff_empty (f : BooleanFunc n) :
    fourierCoeff f ∅ = expect f := by
  simp [fourierCoeff, innerProduct, chiS, expect, uniformWeight]

/-! ## Fourier inversion (Walsh expansion) -/

/-- Key identity: `∑_{S ⊆ [n]} ∏_{i∈S} c_i = ∏_i (1 + c_i)`.
  Used via `Finset.prod_one_add`. -/
private lemma sum_prod_subset_eq_prod_one_add (c : Fin n → ℝ) :
    ∑ S : Finset (Fin n), ∏ i ∈ S, c i =
    ∏ i : Fin n, (1 + c i) := by
  -- Use Finset.prod_one_add: ∏_{i∈s} (1 + f i) = ∑_{t∈s.powerset} ∏_{i∈t} f i
  rw [Finset.prod_one_add Finset.univ]
  -- Now RHS = ∑ t ∈ Finset.univ.powerset, ∏ i ∈ t, c i
  -- Reindex: Finset.univ.powerset ≅ all Finset (Fin n) via id
  apply Finset.sum_nbij id
  · intro t _; exact Finset.mem_powerset.mpr (Finset.subset_univ t)
  · intro t₁ _ t₂ _ h; exact h
  · intro t ht; exact ⟨t, Finset.mem_univ t, rfl⟩
  · intro t _; rfl

/-- The sum of `χ_S(x) * χ_S(y)` over all `S ⊆ [n]` equals `2ⁿ` if `x = y`, else `0`.
  This is the completeness kernel for the Walsh basis. -/
private lemma sum_chiS_mul_eq (x y : BoolCube n) :
    ∑ S : Finset (Fin n), chiS S x * chiS S y = if x = y then (2 : ℝ) ^ n else 0 := by
  simp only [chiS, ← Finset.prod_mul_distrib]
  rw [sum_prod_subset_eq_prod_one_add]
  split_ifs with hxy
  · subst hxy; simp only [boolToSign_mul_self]
    simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
    norm_num
  · obtain ⟨i, hi⟩ := Function.ne_iff.mp hxy
    apply Finset.prod_eq_zero (Finset.mem_univ i)
    have : boolToSign (x i) * boolToSign (y i) = -1 := by
      cases hxi : x i <;> cases hyi : y i <;> simp_all [boolToSign]
    simp [this]

/-- **Walsh Expansion**: every Boolean function `f : {0,1}ⁿ → ℝ` can be written as
  `f(x) = ∑_{S ⊆ [n]} f̂(S) · χ_S(x)`.

  This is the Fourier inversion formula for the uniform measure on `{0,1}ⁿ`. -/
theorem walsh_expansion (f : BooleanFunc n) (x : BoolCube n) :
    f x = ∑ S : Finset (Fin n), fourierCoeff f S * chiS S x := by
  simp only [fourierCoeff, innerProduct, expect, uniformWeight]
  -- Goal: f x = ∑_S (2⁻ⁿ * ∑_y f(y) * χ_S(y)) * χ_S(x)
  -- Proof: show both sides equal 2⁻ⁿ * ∑_y f(y) * ∑_S χ_S(y) * χ_S(x)
  --        then use the completeness kernel
  symm
  calc ∑ S : Finset (Fin n), ((2:ℝ)⁻¹^n * ∑ y, f y * chiS S y) * chiS S x
      = (2:ℝ)⁻¹^n * ∑ y : BoolCube n, ∑ S : Finset (Fin n), f y * (chiS S y * chiS S x) := by
        -- Move 2⁻¹^n outside by rearranging: ∑_S (a * b_S) * c_S = a * ∑_S b_S * c_S,
        -- then swap sum order and distribute f y
        have step1 : ∑ S : Finset (Fin n), ((2:ℝ)⁻¹^n * ∑ y, f y * chiS S y) * chiS S x =
            (2:ℝ)⁻¹^n * ∑ S : Finset (Fin n), (∑ y, f y * chiS S y) * chiS S x := by
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl; intro S _; ring
        have step2 : ∑ S : Finset (Fin n), (∑ y, f y * chiS S y) * chiS S x =
            ∑ y : BoolCube n, ∑ S : Finset (Fin n), f y * (chiS S y * chiS S x) := by
          simp_rw [Finset.sum_mul]
          rw [Finset.sum_comm]
          apply Finset.sum_congr rfl; intro y _
          apply Finset.sum_congr rfl; intro S _; ring
        rw [step1, step2]
    _ = (2:ℝ)⁻¹^n * ∑ y : BoolCube n, f y * (∑ S, chiS S y * chiS S x) := by
        congr 1
        apply Finset.sum_congr rfl; intro y _
        rw [← Finset.mul_sum]
    _ = (2:ℝ)⁻¹^n * ∑ y : BoolCube n, f y * (if y = x then (2:ℝ)^n else 0) := by
        simp_rw [sum_chiS_mul_eq]
    _ = (2:ℝ)⁻¹^n * (f x * (2:ℝ)^n) := by
        congr 1
        simp [Finset.sum_ite_eq', Finset.mem_univ]
    _ = f x := by
        rw [← mul_assoc, mul_comm ((2:ℝ)⁻¹^n) (f x), mul_assoc, ← mul_pow,
            inv_mul_cancel₀ (by norm_num : (2:ℝ) ≠ 0), one_pow, mul_one]

/-`Maximum Degree of Boolean Function`-/
def has_degree_at_most {n : ℕ} (f : (BooleanFunc n)) (k : ℕ) : Prop :=
  ∀ S, f ̂( S ) ≠ 0 → S.card ≤ k

/-! ## Parseval's identity -/

-- Parseval is stated here but proved after fourier_coeff_chi (orthonormality)

/-! ## Orthonormality of Walsh characters -/

/-- The sum of `boolToSign` over all bits is zero. -/
@[simp]
private lemma sum_boolToSign : ∑ b : Bool, boolToSign b = 0 := by
  simp [boolToSign]

/-- Summing `χ_S` over the entire hypercube gives `2ⁿ` if `S = ∅`, else `0`. -/
private lemma sum_chiS (S : Finset (Fin n)) :
    ∑ x : BoolCube n, chiS S x = if S = ∅ then 2 ^ n else 0 := by
  simp only [chiS]
  by_cases hS : S = ∅
  · subst hS; simp [Fintype.card_pi, Fintype.card_bool]
  · simp only [hS, if_false]
    have factored : ∑ x : BoolCube n, ∏ i ∈ S, boolToSign (x i) =
        ∑ x : BoolCube n, ∏ i : Fin n, (if i ∈ S then boolToSign (x i) else 1) := by
      congr 1; ext x; rw [← Finset.prod_filter]; simp
    rw [factored]
    -- Goal: ∑ x : BoolCube n, ∏ i : Fin n, g i (x i) = 0
    -- where g i b = if i ∈ S then boolToSign b else 1
    -- Factor: = ∏ i : Fin n, ∑ b : Bool, g i b  (by Fintype.prod_sum reversed)
    rw [show ∑ x : BoolCube n, ∏ i : Fin n, (if i ∈ S then boolToSign (x i) else 1) =
        ∏ i : Fin n, ∑ b : Bool, (if i ∈ S then boolToSign b else 1) from
      (Fintype.prod_sum (fun i b => if i ∈ S then boolToSign b else 1)).symm]
    obtain ⟨i, hi⟩ := Finset.nonempty_iff_ne_empty.mpr hS
    apply Finset.prod_eq_zero (Finset.mem_univ i)
    simp [hi]

/-- **Orthonormality**: `⟪χ_S, χ_T⟫ = [S = T]`.

  The Walsh characters form an orthonormal system in `L²({0,1}ⁿ, uniform)`. -/
theorem fourier_coeff_chi (S T : Finset (Fin n)) :
    innerProduct (chiS S) (chiS T) = if S = T then 1 else 0 := by
  simp only [innerProduct, expect, uniformWeight]
  have step : ∑ x : BoolCube n, chiS S x * chiS T x =
      ∑ x : BoolCube n, chiS (symmDiff S T) x := by
    congr 1; ext x; exact chiS_mul_chiS S T x
  rw [step, sum_chiS]
  by_cases hst : S = T
  · -- S = T: symmDiff S T = ∅
    subst hst
    simp only [symmDiff_self, Finset.bot_eq_empty, ↓reduceIte]
    rw [← mul_pow]; norm_num
  · -- S ≠ T: symmDiff S T ≠ ∅
    have hd : symmDiff S T ≠ ∅ := by
      intro h
      apply hst
      have : symmDiff S T = ⊥ := by rwa [Finset.bot_eq_empty]
      exact symmDiff_eq_bot.mp this
    simp [hd, hst]

/-- Self inner product of a Walsh character is `1`. -/
@[simp]
lemma innerProduct_chi_self (S : Finset (Fin n)) :
    innerProduct (chiS S) (chiS S) = 1 := by
  simp [fourier_coeff_chi]

/-- **Parseval's Identity**: `‖f‖² = ∑_{S ⊆ [n]} f̂(S)²`.

  The sum of squared Fourier coefficients equals the squared `L²` norm. -/
theorem parseval (f : BooleanFunc n) :
    innerProduct f f = ∑ S : Finset (Fin n), fourierCoeff f S ^ 2 := by
  -- Expand f = ∑_S f̂(S) χ_S and use bilinearity + orthonormality
  have expand : innerProduct f f =
      ∑ S : Finset (Fin n), ∑ T : Finset (Fin n),
        fourierCoeff f S * fourierCoeff f T * innerProduct (chiS S) (chiS T) := by
    -- Expand innerProduct and uniformWeight first so f x * f x becomes visible
    simp_rw [innerProduct, expect, uniformWeight]
    -- Now rewrite f(x)*f(x) using walsh_expansion
    simp_rw [show ∀ x : BoolCube n, f x * f x =
        (∑ S : Finset (Fin n), fourierCoeff f S * chiS S x) *
        (∑ T : Finset (Fin n), fourierCoeff f T * chiS T x) from fun x => by
      rw [← walsh_expansion f x]]
    -- Goal: 2⁻¹^n * ∑_x (∑_S ...) * (∑_T ...) = ∑_S ∑_T f̂S * f̂T * (2⁻¹^n * ∑_x χSx * χTx)
    -- Use the rearrangement:
    rw [show (2:ℝ)⁻¹^n * ∑ x : BoolCube n,
        (∑ S : Finset (Fin n), fourierCoeff f S * chiS S x) *
        (∑ T : Finset (Fin n), fourierCoeff f T * chiS T x) =
        ∑ S : Finset (Fin n), ∑ T : Finset (Fin n),
          fourierCoeff f S * fourierCoeff f T * ((2:ℝ)⁻¹^n * ∑ x : BoolCube n, chiS S x * chiS T x) from by
      -- Step 1: move 2⁻¹^n inside x-sum
      rw [Finset.mul_sum]
      -- Goal: ∑_x 2⁻¹^n * ((∑_S ...) * (∑_T ...)) = ∑_S ∑_T f̂S * f̂T * (...)
      -- Step 2: per x, expand products of sums and collect:
      -- ∑_x 2⁻¹^n * (∑_S ∑_T f̂S * χSx * (f̂T * χTx)) = ∑_S ∑_T f̂S * f̂T * (2⁻¹^n * ∑_x χSx*χTx)
      -- Step 2a: expand per-x product to ∑_x ∑_S ∑_T
      rw [show ∑ x : BoolCube n, (2:ℝ)⁻¹^n *
          ((∑ S : Finset (Fin n), fourierCoeff f S * chiS S x) *
          (∑ T : Finset (Fin n), fourierCoeff f T * chiS T x)) =
          ∑ x : BoolCube n, ∑ S : Finset (Fin n), ∑ T : Finset (Fin n),
            (2:ℝ)⁻¹^n * (fourierCoeff f S * chiS S x * (fourierCoeff f T * chiS T x)) from by
        apply Finset.sum_congr rfl; intro x _
        rw [Finset.sum_mul, Finset.mul_sum]
        apply Finset.sum_congr rfl; intro S _
        rw [show (2:ℝ)⁻¹^n * (fourierCoeff f S * chiS S x * ∑ T, fourierCoeff f T * chiS T x) =
            ∑ T, (2:ℝ)⁻¹^n * (fourierCoeff f S * chiS S x * (fourierCoeff f T * chiS T x)) from by
          rw [show fourierCoeff f S * chiS S x * ∑ T, fourierCoeff f T * chiS T x =
              ∑ T, fourierCoeff f S * chiS S x * (fourierCoeff f T * chiS T x) from Finset.mul_sum _ _ _]
          rw [Finset.mul_sum]]]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl; intro S _
      -- Step 2c: swap x and T
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl; intro T _
      -- Step 2d: factor out f̂S * f̂T
      rw [show ∑ x : BoolCube n, (2:ℝ)⁻¹^n * (fourierCoeff f S * chiS S x * (fourierCoeff f T * chiS T x)) =
          fourierCoeff f S * fourierCoeff f T * ((2:ℝ)⁻¹^n * ∑ x : BoolCube n, chiS S x * chiS T x) from by
        rw [show ∑ x : BoolCube n, (2:ℝ)⁻¹^n * (fourierCoeff f S * chiS S x * (fourierCoeff f T * chiS T x)) =
            ∑ x : BoolCube n, (fourierCoeff f S * fourierCoeff f T) * ((2:ℝ)⁻¹^n * (chiS S x * chiS T x)) from by
          apply Finset.sum_congr rfl; intro x _; ring]
        rw [← Finset.mul_sum, ← Finset.mul_sum]]]
  rw [expand]
  simp_rw [fourier_coeff_chi, mul_ite, mul_one, mul_zero]
  simp_rw [Finset.sum_ite_eq, Finset.mem_univ, if_true]
  apply Finset.sum_congr rfl; intro S _; ring

/-- **Plancherel's Identity**: `⟪f, g⟫ = ∑_{S ⊆ [n]} f̂(S)ĝ(S)`
  The sum of the products of Fourier coefficients equals the inner product -/
theorem plancherel (f g : BooleanFunc n) :
  innerProduct f g = ∑ S : Finset (Fin n), fourierCoeff f S * fourierCoeff g S := by
  -- Expand f and g, and use bilinearity + orthonormality
  have expand : innerProduct f g =
      ∑ S : Finset (Fin n), ∑ T : Finset (Fin n),
        fourierCoeff f S * fourierCoeff g T * innerProduct (chiS S) (chiS T) := by
    -- The exact same expansion logic you used in Parseval, just with `f(x) * g(x)`
    simp_rw [innerProduct, expect, uniformWeight]
    simp_rw [show ∀ x : BoolCube n, f x * g x =
        (∑ S : Finset (Fin n), fourierCoeff f S * chiS S x) *
        (∑ T : Finset (Fin n), fourierCoeff g T * chiS T x) from fun x => by
      rw [← walsh_expansion f x, ← walsh_expansion g x]]
    -- ... (Proceed with the exact same Finset sum rearrangement steps from parseval) ...
    rw [show (2:ℝ)⁻¹^n * ∑ x : BoolCube n,
        (∑ S : Finset (Fin n), fourierCoeff f S * chiS S x) *
        (∑ T : Finset (Fin n), fourierCoeff g T * chiS T x) =
        ∑ S : Finset (Fin n), ∑ T : Finset (Fin n),
          fourierCoeff f S * fourierCoeff g T * ((2:ℝ)⁻¹^n * ∑ x : BoolCube n, chiS S x * chiS T x) from by
      -- Step 1: move 2⁻¹^n inside x-sum
      rw [Finset.mul_sum]
      rw [show ∑ x : BoolCube n, (2:ℝ)⁻¹^n *
          ((∑ S : Finset (Fin n), fourierCoeff f S * chiS S x) *
          (∑ T : Finset (Fin n), fourierCoeff g T * chiS T x)) =
          ∑ x : BoolCube n, ∑ S : Finset (Fin n), ∑ T : Finset (Fin n),
            (2:ℝ)⁻¹^n * (fourierCoeff f S * chiS S x * (fourierCoeff g T * chiS T x)) from by
        apply Finset.sum_congr rfl; intro x _
        rw [Finset.sum_mul, Finset.mul_sum]
        apply Finset.sum_congr rfl; intro S _
        rw [show (2:ℝ)⁻¹^n * (fourierCoeff f S * chiS S x * ∑ T, fourierCoeff g T * chiS T x) =
            ∑ T, (2:ℝ)⁻¹^n * (fourierCoeff f S * chiS S x * (fourierCoeff g T * chiS T x)) from by
          rw [show fourierCoeff f S * chiS S x * ∑ T, fourierCoeff g T * chiS T x =
              ∑ T, fourierCoeff f S * chiS S x * (fourierCoeff g T * chiS T x) from Finset.mul_sum _ _ _]
          rw [Finset.mul_sum]]]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl; intro S _
      -- Step 2c: swap x and T
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl; intro T _
      rw [show ∑ x : BoolCube n, (2:ℝ)⁻¹^n * (fourierCoeff f S * chiS S x * (fourierCoeff g T * chiS T x)) =
          fourierCoeff f S * fourierCoeff g T * ((2:ℝ)⁻¹^n * ∑ x : BoolCube n, chiS S x * chiS T x) from by
        rw [show ∑ x : BoolCube n, (2:ℝ)⁻¹^n * (fourierCoeff f S * chiS S x * (fourierCoeff g T * chiS T x)) =
            ∑ x : BoolCube n, (fourierCoeff f S * fourierCoeff g T) * ((2:ℝ)⁻¹^n * (chiS S x * chiS T x)) from by
          apply Finset.sum_congr rfl; intro x _; ring]
        rw [← Finset.mul_sum, ← Finset.mul_sum]]]
  rw [expand]
  simp_rw [fourier_coeff_chi, mul_ite, mul_one, mul_zero]
  simp_rw [Finset.sum_ite_eq, Finset.mem_univ, if_true]

/-- Flip the `i`-th bit of `x : {0,1}ⁿ`. -/
def flipBit (x : BoolCube n) (i : Fin n) : BoolCube n :=
  Function.update x i (!x i)

@[simp]
lemma flipBit_flipBit (x : BoolCube n) (i : Fin n) : flipBit (flipBit x i) i = x := by
  ext j
  simp [flipBit, Function.update]
  split_ifs with h
  · subst h; simp
  · rfl

lemma flipBit_ne (x : BoolCube n) (i j : Fin n) (h : i ≠ j) :
    flipBit x i j = x j := by
  simp [flipBit, Function.update_of_ne (Ne.symm h)]

/-! ## Influence of a coordinate -/

/-- The **influence** of coordinate `i` on `f`:
  `Inf_i[f] = Pr_x[f(x) ≠ f(xⁱ)]`
  where `xⁱ` denotes `x` with the `i`-th bit flipped.

  For `{-1,1}`-valued functions this equals `𝔼[(f(x) - f(xⁱ))² / 4]`. -/
noncomputable def influence (i : Fin n) (f : BooleanFunc n) : ℝ :=
  expect (fun x ↦ (f x - f (flipBit x i)) ^ 2 / 4)

/-- The **total influence** of `f`:
  `I[f] = ∑_{i=1}^{n} Inf_i[f]`. -/
noncomputable def totalInfluence (f : BooleanFunc n) : ℝ :=
  ∑ i : Fin n, influence i f

/-- Flipping bit `i` negates `χ_S` when `i ∈ S`, and leaves it unchanged when `i ∉ S`. -/
private lemma chiS_flipBit (S : Finset (Fin n)) (x : BoolCube n) (i : Fin n) :
    chiS S (flipBit x i) = if i ∈ S then -chiS S x else chiS S x := by
  simp only [chiS, flipBit]
  by_cases hiS : i ∈ S
  · simp only [hiS, ↓reduceIte]
    -- Rewrite ∏_{j∈S} boolToSign(update x i (!xi) j) using prod_update_of_mem
    have flipped_prod : ∏ j ∈ S, boolToSign (Function.update x i (!x i) j) =
        boolToSign (!x i) * ∏ j ∈ S \ {i}, boolToSign (x j) := by
      have : ∏ j ∈ S, boolToSign (Function.update x i (!x i) j) =
          ∏ j ∈ S, Function.update (fun j => boolToSign (x j)) i (boolToSign (!x i)) j := by
        apply Finset.prod_congr rfl; intro j _
        simp only [Function.update_apply]
        split_ifs with h
        · subst h; rfl
        · rfl
      rw [this]
      exact Finset.prod_update_of_mem hiS _ _
    have orig_prod : ∏ j ∈ S, boolToSign (x j) =
        boolToSign (x i) * ∏ j ∈ S \ {i}, boolToSign (x j) := by
      rw [← Finset.mul_prod_erase _ _ hiS]
      simp [Finset.erase_eq]
    have hneg : boolToSign (!x i) = -boolToSign (x i) := by cases x i <;> simp [boolToSign]
    rw [flipped_prod, orig_prod, hneg]; ring
  · simp only [hiS, ↓reduceIte]
    apply Finset.prod_congr rfl; intro j hj
    have hji : j ≠ i := fun h => hiS (h ▸ hj)
    simp [Function.update_of_ne hji]

/-- The influence of `i` on the Walsh character `χ_S` is `[i ∈ S]`. -/
lemma influence_chi (i : Fin n) (S : Finset (Fin n)) :
    influence i (chiS S) = if i ∈ S then 1 else 0 := by
  simp only [influence, expect, uniformWeight]
  by_cases hiS : i ∈ S
  · simp only [hiS, ↓reduceIte]
    have step : ∀ x : BoolCube n,
        (chiS S x - chiS S (flipBit x i)) ^ 2 / 4 = 1 := by
      intro x
      simp only [chiS_flipBit, hiS, ↓reduceIte]
      have := chiS_sq_eq_one S x
      set c := chiS S x
      have hc : c ^ 2 = 1 := this
      field_simp
      nlinarith [hc, sq_nonneg c]
    simp_rw [step]
    simp only [Finset.sum_const, Finset.card_univ]
    rw [Fintype.card_pi]
    simp only [Fintype.card_bool, Finset.prod_const, Finset.card_fin]
    -- Goal: 2⁻¹^n * 2^n • 1 = 1
    rw [nsmul_eq_mul, mul_one]
    push_cast
    rw [← mul_pow, inv_mul_cancel₀ (by norm_num : (2:ℝ) ≠ 0), one_pow]
  · simp only [hiS, ↓reduceIte]
    have step : ∀ x : BoolCube n, (chiS S x - chiS S (flipBit x i)) ^ 2 / 4 = 0 := by
      intro x
      simp only [chiS_flipBit, hiS, if_false, sub_self, zero_pow (by norm_num : 2 ≠ 0), zero_div]
    simp [step]

/-- **Influence via Fourier**: `Inf_i[f] = ∑_{S ∋ i} f̂(S)²`. -/
theorem influence_eq_sum_fourier (i : Fin n) (f : BooleanFunc n) :
    influence i f = ∑ S : Finset (Fin n), if i ∈ S then fourierCoeff f S ^ 2 else 0 := by
  -- Key: f(x) - f(flipBit x i) = 2 * ∑_{S∋i} f̂(S) * χ_S(x)
  have key : ∀ x : BoolCube n,
      f x - f (flipBit x i) =
      2 * ∑ S : Finset (Fin n), if i ∈ S then fourierCoeff f S * chiS S x else 0 := by
    intro x
    rw [show f x = ∑ S, fourierCoeff f S * chiS S x from walsh_expansion f x,
        show f (flipBit x i) = ∑ S, fourierCoeff f S * chiS S (flipBit x i) from walsh_expansion f _,
        ← Finset.sum_sub_distrib]
    simp_rw [← mul_sub, chiS_flipBit]
    -- Goal: ∑ S, f̂(S) * (χ_S(x) - if i∈S then -χ_S(x) else χ_S(x)) = 2 * ∑_{S∋i} f̂(S)*χ_S(x)
    trans (∑ S : Finset (Fin n), if i ∈ S then 2 * (fourierCoeff f S * chiS S x) else 0)
    · apply Finset.sum_congr rfl; intro S _
      by_cases hiS : i ∈ S <;> simp [hiS, two_mul]
      ring
    · rw [show ∑ S : Finset (Fin n), (if i ∈ S then 2 * (fourierCoeff f S * chiS S x) else 0) =
          2 * ∑ S : Finset (Fin n), if i ∈ S then fourierCoeff f S * chiS S x else 0 from by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl; intro S _
        split_ifs <;> ring]
  -- Define g(x) = ∑_{S∋i} f̂(S) * χ_S(x)
  -- influence i f = 𝔼[(2g(x))²/4] = 𝔼[g(x)²] = innerProduct g g = ∑_{S∋i} f̂(S)² by Parseval
  simp only [influence, expect, uniformWeight]
  simp_rw [key]
  simp_rw [show ∀ x : BoolCube n,
      (2 * ∑ S, if i ∈ S then fourierCoeff f S * chiS S x else 0) ^ 2 / 4 =
      (∑ S, if i ∈ S then fourierCoeff f S * chiS S x else 0) ^ 2 from fun x => by ring]
  -- Rewrite as innerProduct g g where g = ∑_S (if i∈S then f̂(S) else 0) * χ_S
  rw [show (2:ℝ)⁻¹^n * ∑ x : BoolCube n,
      (∑ S, if i ∈ S then fourierCoeff f S * chiS S x else 0) ^ 2 =
      innerProduct (fun x => ∑ S, (if i ∈ S then fourierCoeff f S else 0) * chiS S x)
                   (fun x => ∑ S, (if i ∈ S then fourierCoeff f S else 0) * chiS S x) from by
    simp only [innerProduct, expect, uniformWeight, sq]
    congr 1
    apply Finset.sum_congr rfl; intro x _
    congr 1
    · apply Finset.sum_congr rfl; intro S _; by_cases hiS : i ∈ S <;> simp [hiS]
    · apply Finset.sum_congr rfl; intro S _; by_cases hiS : i ∈ S <;> simp [hiS]]
  -- Apply Parseval: innerProduct g g = ∑_S (f̂_g(S))^2
  rw [parseval]
  -- Compute: f̂_g(S) = if i∈S then f̂(S) else 0
  apply Finset.sum_congr rfl; intro S _
  have hfc : fourierCoeff (fun x => ∑ T, (if i ∈ T then fourierCoeff f T else 0) * chiS T x) S =
      if i ∈ S then fourierCoeff f S else 0 := by
    simp only [fourierCoeff, innerProduct, expect, uniformWeight]
    -- After unfolding, fourierCoeff f T = 2⁻ⁿ * ∑_y f(y) * χ_T(y), which appears in the goal
    -- Goal: 2⁻¹^n * ∑ y ∑ x (if i∈y then ...) * χ_y x * χ_S x = if i∈S then f̂(S) else 0
    -- Rearrange: swap x and T sums, then pull out 2⁻¹^n
    rw [show (2:ℝ)⁻¹^n * ∑ x : BoolCube n,
        (∑ T, (if i ∈ T then 2⁻¹^n * ∑ y : BoolCube n, f y * chiS T y else 0) * chiS T x) * chiS S x =
        ∑ T : Finset (Fin n), (if i ∈ T then 2⁻¹^n * ∑ y : BoolCube n, f y * chiS T y else 0) *
          ((2:ℝ)⁻¹^n * ∑ x, chiS T x * chiS S x) from by
      -- Rearrange: distribute 2⁻¹^n inside, expand T-sum, swap sums
      rw [show (2:ℝ)⁻¹^n * ∑ x : BoolCube n,
          (∑ T, (if i ∈ T then 2⁻¹^n * ∑ y : BoolCube n, f y * chiS T y else 0) * chiS T x) * chiS S x =
          ∑ x : BoolCube n, ∑ T : Finset (Fin n),
            (if i ∈ T then 2⁻¹^n * ∑ y : BoolCube n, f y * chiS T y else 0) *
            ((2:ℝ)⁻¹^n * (chiS T x * chiS S x)) from by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl; intro x _
        rw [Finset.sum_mul, Finset.mul_sum]
        apply Finset.sum_congr rfl; intro T _; ring]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl; intro T _
      rw [← Finset.mul_sum, ← Finset.mul_sum]]
    simp_rw [show ∀ T : Finset (Fin n),
        (2:ℝ)⁻¹^n * ∑ x, chiS T x * chiS S x = if T = S then 1 else 0 from fun T => by
      rw [show (2:ℝ)⁻¹^n * ∑ x, chiS T x * chiS S x =
          innerProduct (chiS T) (chiS S) from by simp [innerProduct, expect, uniformWeight]]
      exact fourier_coeff_chi T S]
    simp only [mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true]
  rw [hfc]
  by_cases hiS : i ∈ S <;> simp [hiS]

/-- **Total Influence via Fourier**: `I[f] = ∑_S |S| · f̂(S)²`. -/
theorem totalInfluence_eq_sum_sq_deg (f : BooleanFunc n) :
    totalInfluence f = ∑ S : Finset (Fin n), S.card * fourierCoeff f S ^ 2 := by
  simp only [totalInfluence, influence_eq_sum_fourier]
  rw [Finset.sum_comm]
  congr 1; ext S
  simp [Finset.sum_ite_mem, Finset.sum_const, nsmul_eq_mul]


/-! ## Discrete Derivative Operator -/

/-- The **derivative** of  a boolean func `f` at `i` is a function
`f'(x) = (f(x⁺ⁱ) - f(x⁻ⁱ))/2`, where `x⁺ⁱ` denotes `x` being changed to `false` at the `i`th position
`x⁻ⁱ` denotes `x` being changed to `true` at the `i`th position -/
noncomputable def derivative {n : ℕ} (i : Fin n) (f : BooleanFunc n) : BooleanFunc n :=
  fun x => (f (Function.update x i false) - f (Function.update x i true)) / 2

lemma derivative_add {n : ℕ} (i : Fin n) (f g : BooleanFunc n) :
    derivative i (f + g) = derivative i f + derivative i g := by
  ext x
  -- The proof will follow from the linearity of addition and division in ℝ
  simp only [derivative, Pi.add_apply]
  ring

/-- The discrete derivative operator commutes with scalar multiplication. -/
lemma derivative_smul {n : ℕ} (i : Fin n) (c : ℝ) (f : BooleanFunc n) :
    derivative i (c • f) = c • derivative i f := by
  ext x
  -- The proof will follow from the distributivity of multiplication in ℝ
  simp only [derivative, Pi.smul_apply, smul_eq_mul]
  ring

-- Derivative is a linear map
noncomputable def derivativeLm {n : ℕ} (i : Fin n) :
    BooleanFunc n →ₗ[ℝ] BooleanFunc n where
  toFun := derivative i
  map_add' := derivative_add i
  map_smul' := derivative_smul i

/-! ## Expectation Operator -/

/-- The **expectation** of  a boolean func `f` at `i` is a function
`f'(x) = (f(x⁺ⁱ) - f(x⁻ⁱ))/2`, where `x⁺ⁱ` denotes `x` being changed to `false` at the `i`th position
`x⁻ⁱ` denotes `x` being changed to `true` at the `i`th position -/

noncomputable def expectationOperator {n : ℕ} (i : Fin n) (f : BooleanFunc n) : BooleanFunc n :=
  fun x => (f (Function.update x i false) + f (Function.update x i true)) / 2

lemma expectation_add {n : ℕ} (i : Fin n) (f g : BooleanFunc n) :
    expectationOperator i (f + g) = expectationOperator i f + expectationOperator i g := by
  ext x
  -- The proof will follow from the linearity of addition and division in ℝ
  simp only [expectationOperator, Pi.add_apply]
  ring

/-- The discrete derivative operator commutes with scalar multiplication. -/
lemma expectation_smul {n : ℕ} (i : Fin n) (c : ℝ) (f : BooleanFunc n) :
    expectationOperator i (c • f) = c • expectationOperator i f := by
  ext x
  -- The proof will follow from the distributivity of multiplication in ℝ
  simp only [expectationOperator, Pi.smul_apply, smul_eq_mul]
  ring
-- Expectation is a linear map
noncomputable def expectationLm {n : ℕ} (i : Fin n) :
    BooleanFunc n →ₗ[ℝ] BooleanFunc n where
  toFun := expectationOperator i
  map_add' := expectation_add i
  map_smul' := expectation_smul i


/-! ## Noise operator -/

/-- The **noise operator** `T_ρ` with noise rate `ρ ∈ [-1, 1]`:
  `T_ρ f(x) = 𝔼_y[f(y)]` where each coordinate of `y` independently equals
  `x_i` with probability `(1+ρ)/2` and `¬x_i` with probability `(1-ρ)/2`.

  In the Fourier domain: `(T_ρ f)̂(S) = ρ^{|S|} · f̂(S)`. -/
noncomputable def noiseOp (ρ : ℝ) (f : BooleanFunc n) : BooleanFunc n :=
  fun x ↦ ∑ S : Finset (Fin n), ρ ^ S.card * fourierCoeff f S * chiS S x

/-- **Noise operator in Fourier domain**: `(T_ρ f)̂(S) = ρ^{|S|} · f̂(S)`. -/
theorem noiseOp_fourier (ρ : ℝ) (f : BooleanFunc n) (S : Finset (Fin n)) :
    fourierCoeff (noiseOp ρ f) S = ρ ^ S.card * fourierCoeff f S := by
  -- ⟨T_ρ f, χ_S⟩ = 2⁻ⁿ ∑_x (∑_T ρ^|T| f̂(T) χ_T(x)) * χ_S(x)
  --              = ∑_T ρ^|T| f̂(T) * ⟨χ_T, χ_S⟩ = ρ^|S| f̂(S)
  simp only [fourierCoeff, innerProduct, expect, uniformWeight, noiseOp]
  -- After unfolding: goal has (2⁻ⁿ * ∑ y f(y) χ_T(y)) for fourierCoeff f T
  -- Manipulate directly
  -- Goal: 2⁻¹^n * ∑_x (∑_T ρ^T.card * (2⁻¹^n * ∑_y f_y * χ_T_y) * χ_T_x) * χ_S_x
  --     = ρ^S.card * (2⁻¹^n * ∑_y f_y * χ_S_y)
  rw [show (2:ℝ)⁻¹^n * ∑ x : BoolCube n,
      (∑ T : Finset (Fin n), ρ ^ T.card * (2⁻¹^n * ∑ y : BoolCube n, f y * chiS T y) * chiS T x) * chiS S x =
      ∑ T : Finset (Fin n), ρ ^ T.card * (2⁻¹^n * ∑ y : BoolCube n, f y * chiS T y) *
        ((2:ℝ)⁻¹^n * ∑ x : BoolCube n, chiS T x * chiS S x) from by
    -- Step 1: distribute 2⁻¹^n over x-sum
    rw [show (2:ℝ)⁻¹^n * ∑ x : BoolCube n,
        (∑ T : Finset (Fin n), ρ ^ T.card * (2⁻¹^n * ∑ y : BoolCube n, f y * chiS T y) * chiS T x) * chiS S x =
        ∑ x : BoolCube n, (2:ℝ)⁻¹^n *
        ((∑ T : Finset (Fin n), ρ ^ T.card * (2⁻¹^n * ∑ y : BoolCube n, f y * chiS T y) * chiS T x) * chiS S x) from by
      rw [Finset.mul_sum]]
    -- Step 2: distribute over T-sum and rearrange
    rw [show ∑ x : BoolCube n, (2:ℝ)⁻¹^n *
        ((∑ T : Finset (Fin n), ρ ^ T.card * (2⁻¹^n * ∑ y : BoolCube n, f y * chiS T y) * chiS T x) * chiS S x) =
        ∑ x : BoolCube n, ∑ T : Finset (Fin n),
          ρ ^ T.card * (2⁻¹^n * ∑ y : BoolCube n, f y * chiS T y) *
          ((2:ℝ)⁻¹^n * (chiS T x * chiS S x)) from by
      apply Finset.sum_congr rfl; intro x _
      rw [show (2:ℝ)⁻¹^n *
          ((∑ T : Finset (Fin n), ρ ^ T.card * (2⁻¹^n * ∑ y : BoolCube n, f y * chiS T y) * chiS T x) * chiS S x) =
          ∑ T : Finset (Fin n), ρ ^ T.card * (2⁻¹^n * ∑ y : BoolCube n, f y * chiS T y) *
          ((2:ℝ)⁻¹^n * (chiS T x * chiS S x)) from by
        rw [Finset.sum_mul]
        simp_rw [Finset.mul_sum]
        apply Finset.sum_congr rfl; intro T _; ring]]
    -- Step 3: swap x and T sums
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl; intro T _
    -- Step 4: factor out ρ^T.card * f̂(T)
    rw [show ∑ x : BoolCube n, ρ ^ T.card * (2⁻¹^n * ∑ y : BoolCube n, f y * chiS T y) *
        ((2:ℝ)⁻¹^n * (chiS T x * chiS S x)) =
        ρ ^ T.card * (2⁻¹^n * ∑ y : BoolCube n, f y * chiS T y) *
        ((2:ℝ)⁻¹^n * ∑ x, chiS T x * chiS S x) from by
      rw [show ∑ x : BoolCube n, ρ ^ T.card * (2⁻¹^n * ∑ y : BoolCube n, f y * chiS T y) *
          ((2:ℝ)⁻¹^n * (chiS T x * chiS S x)) =
          ∑ x : BoolCube n, (ρ ^ T.card * (2⁻¹^n * ∑ y : BoolCube n, f y * chiS T y) * (2:ℝ)⁻¹^n) *
          (chiS T x * chiS S x) from by
        apply Finset.sum_congr rfl; intro x _; ring]
      rw [← Finset.mul_sum]; ring]]
  simp_rw [show ∀ T : Finset (Fin n),
      (2:ℝ)⁻¹^n * ∑ x, chiS T x * chiS S x = if T = S then 1 else 0 from fun T => by
    rw [show (2:ℝ)⁻¹^n * ∑ x, chiS T x * chiS S x =
        innerProduct (chiS T) (chiS S) from by simp [innerProduct, expect, uniformWeight]]
    exact fourier_coeff_chi T S]
  simp only [mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true]

/-- The noise operator is self-adjoint. -/
lemma noiseOp_self_adjoint (ρ : ℝ) (f g : BooleanFunc n) :
    innerProduct (noiseOp ρ f) g = innerProduct f (noiseOp ρ g) := by
  calc
    innerProduct (noiseOp ρ f) g
      = ∑ S : Finset (Fin n), fourierCoeff (noiseOp ρ f) S * fourierCoeff g S := by
        rw [plancherel]

    _ = ∑ S : Finset (Fin n), (ρ ^ S.card * fourierCoeff f S) * fourierCoeff g S := by
        -- Apply the multiplier property to every term in the sum
        apply Finset.sum_congr rfl
        intro S _
        rw [noiseOp_fourier]

    _ = ∑ S : Finset (Fin n), fourierCoeff f S * (ρ ^ S.card * fourierCoeff g S) := by
        -- Rearrange the multiplication (associativity and commutativity)
        apply Finset.sum_congr rfl
        intro S _
        ring

    _ = ∑ S : Finset (Fin n), fourierCoeff f S * fourierCoeff (noiseOp ρ g) S := by
        -- Fold the multiplier property back up for g
        apply Finset.sum_congr rfl
        intro S _
        rw [noiseOp_fourier]

    _ = innerProduct f (noiseOp ρ g) := by
        -- Apply Plancherel in reverse
        rw [← plancherel]

/-- **Stability formula**: `⟪f, T_ρ f⟫ = ∑_S ρ^{|S|} · f̂(S)²`. -/
theorem stability_formula (ρ : ℝ) (f : BooleanFunc n) :
    innerProduct f (noiseOp ρ f) = ∑ S : Finset (Fin n), ρ ^ S.card * fourierCoeff f S ^ 2 := by
  -- Strategy: expand f in Walsh basis, use noiseOp definition, then apply orthonormality
  -- ⟨f, T_ρ f⟩ = 2⁻ⁿ ∑_x f(x) * (∑_T ρ^|T| f̂(T) χ_T(x))
  --            = 2⁻ⁿ ∑_x (∑_S f̂(S) χ_S(x)) * (∑_T ρ^|T| f̂(T) χ_T(x))
  --            = ∑_S ∑_T f̂(S) * ρ^|T| * f̂(T) * ⟨χ_S, χ_T⟩
  --            = ∑_S ρ^|S| * f̂(S)^2
  simp only [innerProduct, expect, uniformWeight, noiseOp]
  -- Rewrite f(x) = ∑_S f̂(S) * χ_S(x) using walsh_expansion
  simp_rw [show ∀ x : BoolCube n, f x = ∑ S : Finset (Fin n), fourierCoeff f S * chiS S x from
    fun x => walsh_expansion f x]
  rw [show (2:ℝ)⁻¹^n * ∑ x : BoolCube n,
      (∑ S, fourierCoeff f S * chiS S x) *
      (∑ T, ρ^T.card * fourierCoeff f T * chiS T x) =
      ∑ S : Finset (Fin n), ∑ T : Finset (Fin n),
        fourierCoeff f S * (ρ^T.card * fourierCoeff f T) *
        ((2:ℝ)⁻¹^n * ∑ x, chiS S x * chiS T x) from by
    -- Step 1: distribute 2⁻¹^n over x-sum
    rw [show (2:ℝ)⁻¹^n * ∑ x : BoolCube n,
        (∑ S, fourierCoeff f S * chiS S x) * (∑ T, ρ^T.card * fourierCoeff f T * chiS T x) =
        ∑ x : BoolCube n, (2:ℝ)⁻¹^n *
        ((∑ S, fourierCoeff f S * chiS S x) * (∑ T, ρ^T.card * fourierCoeff f T * chiS T x)) from by
      rw [Finset.mul_sum]]
    -- Step 2: expand products of sums
    rw [show ∑ x : BoolCube n, (2:ℝ)⁻¹^n *
        ((∑ S, fourierCoeff f S * chiS S x) * (∑ T, ρ^T.card * fourierCoeff f T * chiS T x)) =
        ∑ x : BoolCube n, ∑ S : Finset (Fin n), ∑ T : Finset (Fin n),
          (2:ℝ)⁻¹^n * (fourierCoeff f S * chiS S x * (ρ^T.card * fourierCoeff f T * chiS T x)) from by
      apply Finset.sum_congr rfl; intro x _
      conv_lhs => rw [Finset.sum_mul, Finset.mul_sum]
      apply Finset.sum_congr rfl; intro S _
      rw [show (2:ℝ)⁻¹^n * (fourierCoeff f S * chiS S x * ∑ T, ρ^T.card * fourierCoeff f T * chiS T x) =
          ∑ T, (2:ℝ)⁻¹^n * (fourierCoeff f S * chiS S x * (ρ^T.card * fourierCoeff f T * chiS T x)) from by
        rw [show fourierCoeff f S * chiS S x * ∑ T, ρ^T.card * fourierCoeff f T * chiS T x =
            ∑ T, fourierCoeff f S * chiS S x * (ρ^T.card * fourierCoeff f T * chiS T x) from Finset.mul_sum _ _ _]
        rw [Finset.mul_sum]]]
    -- Step 3: swap sums: ∑_x ∑_S ∑_T → ∑_S ∑_T ∑_x
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl; intro S _
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl; intro T _
    -- Step 4: factor out constants from x-sum
    rw [show ∑ x : BoolCube n, (2:ℝ)⁻¹^n * (fourierCoeff f S * chiS S x * (ρ^T.card * fourierCoeff f T * chiS T x)) =
        fourierCoeff f S * (ρ^T.card * fourierCoeff f T) * ((2:ℝ)⁻¹^n * ∑ x, chiS S x * chiS T x) from by
      rw [show ∑ x : BoolCube n, (2:ℝ)⁻¹^n * (fourierCoeff f S * chiS S x * (ρ^T.card * fourierCoeff f T * chiS T x)) =
          ∑ x : BoolCube n, (fourierCoeff f S * (ρ^T.card * fourierCoeff f T)) * ((2:ℝ)⁻¹^n * (chiS S x * chiS T x)) from by
        apply Finset.sum_congr rfl; intro x _; ring]
      rw [← Finset.mul_sum, ← Finset.mul_sum]]]
  simp_rw [show ∀ S T : Finset (Fin n),
      (2:ℝ)⁻¹^n * ∑ x, chiS S x * chiS T x = if S = T then 1 else 0 from fun S T => by
    rw [show (2:ℝ)⁻¹^n * ∑ x, chiS S x * chiS T x =
        innerProduct (chiS S) (chiS T) from by simp [innerProduct, expect, uniformWeight]]
    exact fourier_coeff_chi S T]
  simp only [mul_ite, mul_one, mul_zero, Finset.sum_ite_eq, Finset.mem_univ, if_true]
  apply Finset.sum_congr rfl; intro S _; ring

/-! ## Linearity and combinatorial properties -/

/-- Boolean functions form an `ℝ`-vector space. -/
instance : AddCommGroup (BooleanFunc n) := Pi.addCommGroup

noncomputable instance : Module ℝ (BooleanFunc n) := Pi.module _ _ _

/-- The inner product is bilinear in the first argument. -/
lemma innerProduct_add_left (f g h : BooleanFunc n) :
    innerProduct (f + g) h = innerProduct f h + innerProduct g h := by
  simp only [innerProduct, expect, uniformWeight, Pi.add_apply, add_mul]
  rw [Finset.sum_add_distrib, mul_add]

/-- The inner product is symmetric. -/
lemma innerProduct_comm (f g : BooleanFunc n) :
    innerProduct f g = innerProduct g f := by
  simp [innerProduct, expect, mul_comm]

/-- The inner product is nonneg on the diagonal. -/
lemma innerProduct_self_nonneg (f : BooleanFunc n) :
    0 ≤ innerProduct f f := by
  apply mul_nonneg
  · apply pow_nonneg; positivity
  · apply Finset.sum_nonneg
    intro x _; exact mul_self_nonneg (f x)

/-- The Walsh characters `{χ_S}_{S ⊆ [n]}` span `L²({0,1}ⁿ)`.
  There are exactly `2ⁿ` characters, matching the dimension of `L²({0,1}ⁿ) ≅ ℝ^{2ⁿ}`. -/
lemma card_walsh_characters :
    (Finset.univ (α := Finset (Fin n))).card = 2 ^ n := by
  rw [Finset.card_univ, Fintype.card_finset, Fintype.card_fin]

/-! ## Dictator and parity functions -/

/-- The **dictator function** for coordinate `i`: `f(x) = (-1)^{x_i}`.
  Its only nonzero Fourier coefficient is `f̂({i}) = 1`. -/
noncomputable def dictator (i : Fin n) : BooleanFunc n :=
  fun x ↦ boolToSign (x i)

/-- The dictator function equals the Walsh character `χ_{i}`. -/
lemma dictator_eq_chi (i : Fin n) : dictator i = chiS {i} := by
  ext x; simp [dictator, chiS]

/-- The **parity function** `f(x) = (-1)^{x_1 + ⋯ + x_n}`.
  Its only nonzero Fourier coefficient is `f̂([n]) = 1`. -/
noncomputable def parity (n : ℕ) : BooleanFunc n :=
  fun x ↦ ∏ i : Fin n, boolToSign (x i)

/-- The parity function equals `χ_{Finset.univ}`. -/
lemma parity_eq_chi_univ : parity n = chiS Finset.univ := by
  ext x; simp [parity, chiS]

/-- The majority function on `{0,1}^{2k+1}`:
  outputs `1` if more than half the bits are `0`, and `-1` otherwise. -/
noncomputable def majority (k : ℕ) : BooleanFunc (2 * k + 1) :=
  fun x ↦ if (Finset.univ.filter (fun i ↦ x i = false)).card > k then 1 else -1

/-! ## Sensitivity and block sensitivity -/

/-- The **sensitivity** of `f` at `x`: the number of coordinates `i` such that
  flipping bit `i` changes the value of `f`. -/
noncomputable def sensitivity (f : BooleanFunc n) (x : BoolCube n) : ℕ :=
  (Finset.univ.filter (fun i : Fin n ↦ f x ≠ f (flipBit x i))).card

/-- The maximum sensitivity of `f` over all inputs. -/
noncomputable def maxSensitivity (f : BooleanFunc n) : ℕ :=
  Finset.univ.sup (sensitivity f)

/-- Influence bounds sensitivity: `Inf_i[f] ≤ 1`. -/
lemma influence_le_one (i : Fin n) (f : BooleanFunc n) (hf : ∀ x, f x ∈ ({-1, 1} : Set ℝ)) :
    influence i f ≤ 1 := by
  simp only [influence, expect, uniformWeight]
  -- Show 2⁻ⁿ * ∑_x (f x - f(flipBit x i))^2/4 ≤ 2⁻ⁿ * 2^n = 1
  have hcard : (Finset.univ (α := BoolCube n)).card = 2^n := by
    simp [Finset.card_univ, Fintype.card_pi, Fintype.card_bool,
          Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  have hsum : ∑ x : BoolCube n, (f x - f (flipBit x i)) ^ 2 / 4 ≤ 2^n := by
    calc ∑ x : BoolCube n, (f x - f (flipBit x i)) ^ 2 / 4
        ≤ ∑ _x : BoolCube n, (1 : ℝ) := by
          apply Finset.sum_le_sum; intro x _
          have hfx := hf x; have hfflip := hf (flipBit x i)
          simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hfx hfflip
          rcases hfx with h1 | h1 <;> rcases hfflip with h2 | h2 <;> rw [h1, h2] <;> norm_num
      _ = 2^n := by simp [hcard]
  calc (2:ℝ)⁻¹^n * ∑ x : BoolCube n, (f x - f (flipBit x i)) ^ 2 / 4
      ≤ (2:ℝ)⁻¹^n * (2:ℝ)^n := by
        apply mul_le_mul_of_nonneg_left hsum
        apply pow_nonneg; positivity
    _ = 1 := by rw [← mul_pow]; norm_num

/-- For any Boolean function `f`, the maximum individual influence is at least the average: `max_i Inf_i[f] ≥ I[f] / n`. -/
lemma max_influence_lower_bound (f : BooleanFunc n) (hn : 0 < n) :
    ∃ i : Fin n, totalInfluence f / n ≤ influence i f := by
  by_contra h
  push_neg at h
  have hlt : ∀ i : Fin n, influence i f < totalInfluence f / n := h
  have hsum : totalInfluence f = ∑ i : Fin n, influence i f := rfl
  have : totalInfluence f < totalInfluence f := by
    calc totalInfluence f
        = ∑ i : Fin n, influence i f := hsum
      _ < ∑ _i : Fin n, totalInfluence f / n := by
            apply Finset.sum_lt_sum_of_nonempty
            · exact Finset.univ_nonempty_iff.mpr (Fin.pos_iff_nonempty.mp hn)
            · intro i _; exact hlt i
      _ = n * (totalInfluence f / n) := by simp [Finset.sum_const, nsmul_eq_mul]
      _ = totalInfluence f := by field_simp
  exact lt_irrefl _ this

/-! ## Additional lemmas for Arrow's theorem -/

/-- `boolToSign` negates under `Bool.not`. -/
@[simp]
lemma boolToSign_not (b : Bool) : boolToSign (!b) = -boolToSign b := by
  cases b <;> simp [boolToSign]

/-- Flipping all bits of `x` multiplies `χ_S(x)` by `(-1)^|S|`. -/
lemma chiS_neg (S : Finset (Fin n)) (x : BoolCube n) :
    chiS S (fun i => !x i) = (-1 : ℝ) ^ S.card * chiS S x := by
  simp only [chiS]
  simp_rw [boolToSign_not]
  -- ∏_{i∈S} (-boolToSign (x i)) = (-1)^|S| * ∏_{i∈S} boolToSign (x i)
  induction S using Finset.induction with
  | empty => simp
  | insert a s ha ih =>
    rw [Finset.prod_insert ha, Finset.card_insert_of_notMem ha, Finset.prod_insert ha, ih]
    ring

/-- A Boolean function is **odd** if flipping all inputs negates the output.
  Models the antisymmetry requirement in social choice. -/
def isOddFunc (f : BooleanFunc n) : Prop :=
  ∀ x : BoolCube n, f (fun i => !x i) = -f x

/-- A Boolean function takes values in `{-1, 1}`. -/
def isPmOne (f : BooleanFunc n) : Prop :=
  ∀ x : BoolCube n, f x = 1 ∨ f x = -1

/-- For an odd function, the Fourier coefficient at any even-cardinality set is zero. -/
lemma fourierCoeff_odd_even (f : BooleanFunc n) (hodd : isOddFunc f)
    (S : Finset (Fin n)) (heven : Even S.card) :
    fourierCoeff f S = 0 := by
  simp only [fourierCoeff, innerProduct, expect, uniformWeight]
  suffices h : ∑ x : BoolCube n, f x * chiS S x = 0 by simp [h]
  -- The bijection that flips all bits
  let e : BoolCube n ≃ BoolCube n :=
    { toFun    := fun x i => !x i
      invFun   := fun x i => !x i
      left_inv := fun x => by ext; simp
      right_inv := fun x => by ext; simp }
  -- Change of variables: ∑_x f(x) χ_S(x) = ∑_x f(¬x) χ_S(¬x)
  -- Uses that x ↦ (¬x) is a bijection (involution)
  have hcv : ∑ x : BoolCube n, f x * chiS S x =
      ∑ x : BoolCube n, f (fun i => !x i) * chiS S (fun i => !x i) :=
    (Fintype.sum_equiv e
      (fun x => f (fun i => !x i) * chiS S (fun i => !x i))
      (fun x => f x * chiS S x)
      (fun _ => rfl)).symm
  -- Apply oddness and chiS_neg
  have hflip : ∑ x : BoolCube n, f (fun i => !x i) * chiS S (fun i => !x i) =
      -(∑ x : BoolCube n, f x * chiS S x) := by
    -- Expose the universal form so simp_rw can use hodd
    have hodd' : ∀ x : BoolCube n, f (fun i => !x i) = -f x := hodd
    -- (-1)^|S| = 1 when |S| is even
    have hone : (-1 : ℝ) ^ S.card = 1 := by
      obtain ⟨k, hk⟩ := heven
      rw [hk, ← two_mul, pow_mul, show (-1 : ℝ) ^ 2 = 1 from by norm_num, one_pow]
    simp_rw [hodd', chiS_neg, hone, one_mul, neg_mul]
    simp [Finset.sum_neg_distrib]
  linarith [hcv.trans hflip]

/-- For a `±1`-valued function, the `L²` self-inner-product equals `1`. -/
lemma innerProduct_self_pm_one (f : BooleanFunc n) (hf : isPmOne f) :
    innerProduct f f = 1 := by
  simp only [innerProduct, expect, uniformWeight]
  have hsq : ∀ x : BoolCube n, f x * f x = 1 := fun x => by
    rcases hf x with h | h <;> simp [h]
  simp_rw [hsq]
  simp only [Finset.sum_const, Finset.card_univ]
  rw [Fintype.card_pi]
  simp only [Fintype.card_bool, Finset.prod_const, Finset.card_fin]
  rw [nsmul_eq_mul, mul_one]
  push_cast
  rw [← mul_pow, inv_mul_cancel₀ (by norm_num : (2 : ℝ) ≠ 0), one_pow]

/-- **Parseval for `±1`-valued functions**: `∑_S f̂(S)² = 1`. -/
lemma parseval_pm_one (f : BooleanFunc n) (hf : isPmOne f) :
    ∑ S : Finset (Fin n), fourierCoeff f S ^ 2 = 1 := by
  rw [← parseval, innerProduct_self_pm_one f hf]

/-- Fourier weight concentrated on level `k`: `W_k[f] = ∑_{|S|=k} f̂(S)²`. -/
noncomputable def weightLevel (k : ℕ) (f : BooleanFunc n) : ℝ :=
  ∑ S : Finset (Fin n), if S.card = k then fourierCoeff f S ^ 2 else 0

end BooleanAnalysis
