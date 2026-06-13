import TCSlib.BooleanAnalysis.Hypercontractivity.General


/-!
# Small-Set Expansion Theorems via Hypercontractivity

This file proves the **Generalized Small-Set Expansion Theorem** and the
**Small-Set Expansion Theorem**, following the two-function hypercontractivity
approach.

## Main Results

* `generalized_small_set_expansion`: For sets `A, B ⊆ {0,1}ⁿ` with volumes
  `α = μ(A)` and `β = μ(B)`, and parameters `p, q ≥ 1` with `(p-1)(q-1) ≥ ρ²`,
  we have `Pr[x ∈ A, y ∈ B] ≤ α^{1/p} · β^{1/q}`.

* `small_set_expansion`: For a set `A ⊆ {0,1}ⁿ` with volume `α = μ(A)`,
  `Pr[x ∈ A, y ∈ A] ≤ α^{2/(1+ρ)}`.

## References

* Ryan O'Donnell, *Analysis of Boolean Functions*, Cambridge University Press, 2014.
-/

open BooleanAnalysis GeneralHypercontractivity Real

set_option maxHeartbeats 800000

namespace SmallSetExpansion

variable {n : ℕ}

/-! ## Indicator Functions and Volume -/

/-- The indicator function of a set `A ⊆ {0,1}ⁿ`, taking values 0 and 1. -/
noncomputable def setIndicator (A : Finset (BoolCube n)) : BooleanFunc n :=
  fun x => if x ∈ A then 1 else 0

/-- The volume (density) of a set `A ⊆ {0,1}ⁿ` under the uniform measure. -/
noncomputable def volume (A : Finset (BoolCube n)) : ℝ :=
  expect (setIndicator A)

/-! ## Properties of Indicator Functions -/

lemma setIndicator_nonneg (A : Finset (BoolCube n)) (x : BoolCube n) :
    0 ≤ setIndicator A x := by
  simp [setIndicator]; split <;> norm_num

lemma setIndicator_le_one (A : Finset (BoolCube n)) (x : BoolCube n) :
    setIndicator A x ≤ 1 := by
  simp [setIndicator]; split <;> norm_num

lemma abs_setIndicator (A : Finset (BoolCube n)) (x : BoolCube n) :
    |setIndicator A x| = setIndicator A x := by
  rw [abs_of_nonneg (setIndicator_nonneg A x)]

lemma setIndicator_sq (A : Finset (BoolCube n)) (x : BoolCube n) :
    setIndicator A x ^ 2 = setIndicator A x := by
  simp only [setIndicator]; split <;> norm_num

lemma setIndicator_rpow (A : Finset (BoolCube n)) (x : BoolCube n)
    {r : ℝ} (hr : 0 < r) :
    setIndicator A x ^ r = setIndicator A x := by
  simp only [setIndicator]
  split
  · simp [one_rpow]
  · simp [zero_rpow (ne_of_gt hr)]

lemma abs_setIndicator_rpow (A : Finset (BoolCube n)) (x : BoolCube n)
    {r : ℝ} (hr : 0 < r) :
    |setIndicator A x| ^ r = setIndicator A x := by
  rw [abs_setIndicator, setIndicator_rpow A x hr]

/-- The `r`-th moment of an indicator function equals the volume. -/
lemma expect_abs_indicator_rpow (A : Finset (BoolCube n)) {r : ℝ} (hr : 0 < r) :
    expect (fun x => |setIndicator A x| ^ r) = volume A := by
  simp only [volume]
  congr 1
  ext x
  rw [abs_setIndicator_rpow A x hr]

/-- The `L^r` norm of an indicator function: `‖1_A‖_r = μ(A)^{1/r}`. -/
lemma indicator_Lr_norm (A : Finset (BoolCube n)) {r : ℝ} (hr : 0 < r) :
    (expect (fun x => |setIndicator A x| ^ r)) ^ (1 / r) = volume A ^ (1 / r) := by
  rw [expect_abs_indicator_rpow A hr]

/-! ## Volume Properties -/

lemma volume_nonneg (A : Finset (BoolCube n)) : 0 ≤ volume A := by
  unfold volume expect uniformWeight
  apply mul_nonneg
  · positivity
  · exact Finset.sum_nonneg fun x _ => setIndicator_nonneg A x

lemma volume_le_one (A : Finset (BoolCube n)) : volume A ≤ 1 := by
  unfold volume setIndicator;
  unfold expect;
  simp +decide [ uniformWeight ];
  rw [ inv_mul_le_iff₀ ( by positivity ) ];
  exact_mod_cast le_trans ( Finset.card_le_univ _ ) ( by norm_num )

/-! ## Probability as Inner Product -/

/-- `Pr[x ∈ A, y ∈ B] = ⟨1_A, T_ρ 1_B⟩`. -/
lemma prob_eq_innerProduct (ρ : ℝ) (A B : Finset (BoolCube n)) :
    innerProduct (setIndicator A) (noiseOp ρ (setIndicator B)) =
    innerProduct (setIndicator A) (noiseOp ρ (setIndicator B)) := rfl

/-! ## Generalized Small-Set Expansion -/

/--
**Generalized Small-Set Expansion Theorem.**

For sets `A, B ⊆ {0,1}ⁿ` with volumes `α = μ(A)`, `β = μ(B)`, and
parameters `p ≥ 1` and `u ≥ 2` with `ρ ≤ √((p-1)/(u-1))`:

  `⟨1_A, T_ρ 1_B⟩ ≤ α^{(u-1)/u} · β^{1/p}`

Here `(u-1)/u = 1/q` where `q = u/(u-1)` is the Hölder conjugate of `u`.
The condition `ρ ≤ √((p-1)/(u-1))` is equivalent to `(q-1)(p-1) ≥ ρ²`.
-/
theorem generalized_small_set_expansion
    (p u : ℝ) (hp : 1 ≤ p) (hpu : p ≤ u) (hu : 2 ≤ u)
    (ρ : ℝ) (hρ0 : 0 ≤ ρ) (hρ1 : ρ ≤ 1)
    (hρ_bound : ρ ≤ Real.sqrt ((p - 1) / (u - 1)))
    (A B : Finset (BoolCube n)) :
    innerProduct (setIndicator A) (noiseOp ρ (setIndicator B)) ≤
    (volume A) ^ ((u - 1) / u) * (volume B) ^ (1 / p) := by
  convert general_two_function_hypercontractivity p u hp hpu hu ρ hρ0 hρ1 hρ_bound ( setIndicator A ) ( setIndicator B ) using 1;
  rw [ expect_abs_indicator_rpow, expect_abs_indicator_rpow ];
  · linarith;
  · exact div_pos ( by linarith ) ( by linarith )

/--
**Small-Set Expansion Theorem.**

For a set `A ⊆ {0,1}ⁿ` with volume `α = μ(A)` and correlation parameter
`0 < ρ ≤ 1`:

  `⟨1_A, T_ρ 1_A⟩ ≤ α^{2/(1+ρ)}`

This follows from the generalized theorem by setting `B = A` and
optimizing with `p = q = 1 + ρ`, which gives `u = (1+ρ)/ρ`.
-/
theorem small_set_expansion
    (ρ : ℝ) (hρ0 : 0 < ρ) (hρ1 : ρ ≤ 1)
    (A : Finset (BoolCube n)) :
    innerProduct (setIndicator A) (noiseOp ρ (setIndicator A)) ≤
    (volume A) ^ (2 / (1 + ρ)) := by
  convert generalized_small_set_expansion ( 1 + ρ ) ( ( 1 + ρ ) / ρ ) _ _ _ ρ _ _ _ A A using 1 <;> try linarith;
  · rw [ ← Real.rpow_add' ] <;> norm_num;
    · grind;
    · exact volume_nonneg A;
    · grind;
  · rw [ le_div_iff₀ ] <;> nlinarith;
  · rw [ le_div_iff₀ ] <;> linarith;
  · field_simp;
    exact Real.le_sqrt_of_sq_le ( by ring_nf; norm_num )

end SmallSetExpansion
