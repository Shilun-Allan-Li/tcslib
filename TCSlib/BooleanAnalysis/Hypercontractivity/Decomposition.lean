import TCSlib.BooleanAnalysis.Basic

/-!
# Boolean-cube decomposition

Shared infrastructure for inductive arguments on the Boolean cube. This module contains
restriction to the final coordinate, the corresponding average/difference decomposition,
and elementary expectation and Fourier identities.

The declarations remain in the `Bonami` namespace for compatibility with existing users.
-/

namespace Bonami

open BooleanAnalysis

/-- Restrict a Boolean function on `n + 1` variables by fixing the last coordinate. -/
noncomputable def restrictLast {n : ℕ} (f : BooleanFunc (n + 1)) (b : Bool) : BooleanFunc n :=
  fun x => f (Fin.snoc x b)

/-- The average of `f` over the last coordinate. -/
noncomputable def avgLast {n : ℕ} (f : BooleanFunc (n + 1)) : BooleanFunc n :=
  fun x => (restrictLast f false x + restrictLast f true x) / 2

/-- The half-difference of `f` over the last coordinate. -/
noncomputable def diffLast {n : ℕ} (f : BooleanFunc (n + 1)) : BooleanFunc n :=
  fun x => (restrictLast f false x - restrictLast f true x) / 2

/-- Restriction at `false` is the sum of the average and half-difference. -/
lemma restrictLast_false_eq {n : ℕ} (f : BooleanFunc (n + 1)) (x : BoolCube n) :
    restrictLast f false x = avgLast f x + diffLast f x := by
  simp [restrictLast, avgLast, diffLast]
  ring

/-- Restriction at `true` is the average minus the half-difference. -/
lemma restrictLast_true_eq {n : ℕ} (f : BooleanFunc (n + 1)) (x : BoolCube n) :
    restrictLast f true x = avgLast f x - diffLast f x := by
  simp [restrictLast, avgLast, diffLast]
  ring

/-- A sum over `BoolCube (n + 1)` splits according to the final coordinate. -/
lemma sum_boolCube_succ {n : ℕ} (φ : BoolCube (n + 1) → ℝ) :
    ∑ x : BoolCube (n + 1), φ x =
    ∑ x : BoolCube n, φ (Fin.snoc x false) + ∑ x : BoolCube n, φ (Fin.snoc x true) := by
  have h_split :
      ∑ x : BoolCube (n + 1), φ x = ∑ x : BoolCube n × Bool, φ (Fin.snoc x.1 x.2) := by
    apply Finset.sum_bij (fun x _ => (Fin.init x, x (Fin.last n)))
    · simp +zetaDelta at *
    · simp +contextual [funext_iff]
      exact fun a₁ a₂ h₁ h₂ x => by
        cases x using Fin.lastCases <;> simp_all +decide [Fin.init]
    · intro b hb
      use Fin.snoc b.1 b.2
      aesop
    · aesop
  simp_all +decide [← Finset.sum_add_distrib]
  erw [Finset.sum_product]
  exact Finset.sum_congr rfl fun _ _ => by rw [Finset.sum_eq_add] <;> aesop

/-- `uniformWeight (n + 1) = uniformWeight n / 2`. -/
lemma uniformWeight_succ (n : ℕ) :
    uniformWeight (n + 1) = uniformWeight n / 2 := by
  simp [uniformWeight, pow_succ]
  ring

/-- The Fourier coefficient of `avgLast f` at `S` is the lifted coefficient of `f`. -/
lemma fourierCoeff_avgLast {n : ℕ} (f : BooleanFunc (n + 1)) (S : Finset (Fin n)) :
    BooleanAnalysis.fourierCoeff (avgLast f) S =
      BooleanAnalysis.fourierCoeff f (S.image Fin.castSucc) := by
  unfold avgLast
  simp +decide only [BooleanAnalysis.fourierCoeff]
  ring_nf
  unfold innerProduct
  simp +decide only [one_div, mul_comm]
  ring_nf
  unfold expect
  simp +decide only [chiS, restrictLast, one_div, mul_comm, Finset.sum_add_distrib,
    Finset.mul_sum _ _ _, mul_left_comm]
  ring_nf
  rw [add_comm 1 n, uniformWeight_succ, ← mul_add, sum_boolCube_succ]
  ring_nf
  simp +decide [mul_comm, mul_left_comm, Finset.mul_sum _ _ _]

/-- The Fourier coefficient of `diffLast f` at `S` is the lifted coefficient containing
the final coordinate. -/
lemma fourierCoeff_diffLast {n : ℕ} (f : BooleanFunc (n + 1)) (S : Finset (Fin n)) :
    BooleanAnalysis.fourierCoeff (diffLast f) S =
      BooleanAnalysis.fourierCoeff f (S.image Fin.castSucc ∪ {Fin.last n}) := by
  unfold diffLast BooleanAnalysis.fourierCoeff innerProduct expect chiS restrictLast
  rw [uniformWeight_succ]
  rw [show (Finset.univ : Finset (Fin (n + 1) → Bool)) =
    Finset.image (fun x : Fin n → Bool => Fin.snoc x Bool.false) Finset.univ ∪
      Finset.image (fun x : Fin n → Bool => Fin.snoc x Bool.true) Finset.univ from ?_,
    Finset.sum_union]
  · rw [Finset.sum_image, Finset.sum_image] <;>
      norm_num [Finset.prod_union, Finset.prod_image]
    ring_nf
    · simp +decide only [mul_assoc, Finset.sum_add_distrib, Finset.sum_mul _ _ _]
      rw [mul_add]
    · exact fun x y h => by simpa using congrArg Fin.init h
    · exact fun x y h => by simpa using congrArg Fin.init h
  · norm_num [Finset.disjoint_left]
  · ext x
    by_cases hx : x (Fin.last n) <;>
      simp +decide only [Finset.mem_univ, Finset.mem_union, Finset.mem_image, true_and, true_iff]
    · exact Or.inr ⟨fun i => x i.castSucc, by
        ext i
        cases i using Fin.lastCases <;> aesop⟩
    · exact Or.inl ⟨fun i => x i.castSucc, by
        ext i
        cases i using Fin.lastCases <;> aesop⟩

/-- Expectation on `BoolCube (n + 1)` is the average over the two restrictions. -/
lemma expect_succ_eq {n : ℕ} (φ : BooleanFunc (n + 1)) :
    expect φ = (expect (restrictLast φ false) + expect (restrictLast φ true)) / 2 := by
  unfold expect restrictLast
  rw [sum_boolCube_succ, uniformWeight_succ]
  ring

/-- `(a + b)⁴ + (a - b)⁴ = 2(a⁴ + 6a²b² + b⁴)`. -/
lemma fourth_pow_sum (a b : ℝ) :
    (a + b) ^ 4 + (a - b) ^ 4 = 2 * (a ^ 4 + 6 * a ^ 2 * b ^ 2 + b ^ 4) := by
  ring

/-- `(a + b)² + (a - b)² = 2(a² + b²)`. -/
lemma second_pow_sum (a b : ℝ) :
    (a + b) ^ 2 + (a - b) ^ 2 = 2 * (a ^ 2 + b ^ 2) := by
  ring

/-- Fourth-moment decomposition along the final coordinate. -/
lemma fourth_moment_decomp {n : ℕ} (f : BooleanFunc (n + 1)) :
    expect (fun x => f x ^ 4) =
    expect (fun x => avgLast f x ^ 4) +
      6 * expect (fun x => avgLast f x ^ 2 * diffLast f x ^ 2) +
      expect (fun x => diffLast f x ^ 4) := by
  have h_decomp :
      expect (fun x => f x ^ 4) =
        expect (fun x => (avgLast f x + diffLast f x) ^ 4) / 2 +
        expect (fun x => (avgLast f x - diffLast f x) ^ 4) / 2 := by
    convert expect_succ_eq (fun x => f x ^ 4) using 1
    unfold expect restrictLast avgLast diffLast
    ring_nf
    rfl
  rw [h_decomp]
  ring_nf
  norm_num [Finset.sum_add_distrib, Finset.mul_sum _ _ _, Finset.sum_mul]
  ring_nf
  unfold expect
  norm_num [Finset.sum_add_distrib, Finset.mul_sum _ _ _, Finset.sum_mul]
  ring_nf
  simpa only [mul_assoc, ← Finset.mul_sum _ _ _, ← Finset.sum_mul] using by ring

/-- Second-moment decomposition along the final coordinate. -/
lemma second_moment_decomp {n : ℕ} (f : BooleanFunc (n + 1)) :
    expect (fun x => f x ^ 2) =
      expect (fun x => avgLast f x ^ 2) + expect (fun x => diffLast f x ^ 2) := by
  unfold expect
  ring_nf
  have h_expand :
      ∑ x : BoolCube (n + 1), f x ^ 2 =
        ∑ x : BoolCube n, (avgLast f x + diffLast f x) ^ 2 +
        ∑ x : BoolCube n, (avgLast f x - diffLast f x) ^ 2 := by
    convert sum_boolCube_succ (fun x => f x ^ 2) using 1
    congr! 2
    · exact congr_arg (· ^ 2) (by
        unfold avgLast diffLast restrictLast
        ring)
    · simpa only [restrictLast] using
        congrArg (fun y : ℝ => y ^ 2) (restrictLast_true_eq f _).symm
  simp_all +decide [add_sq, sub_sq, Finset.sum_add_distrib, Finset.mul_sum _ _ _]
  ring_nf
  norm_num [← Finset.mul_sum _ _ _, ← Finset.sum_mul, uniformWeight]
  ring

/-- Cauchy–Schwarz for expectations: `E[g²h²]² ≤ E[g⁴]E[h⁴]`. -/
lemma expect_cs_sq {n : ℕ} (g h : BooleanFunc n) :
    expect (fun x => g x ^ 2 * h x ^ 2) ^ 2 ≤
      expect (fun x => g x ^ 4) * expect (fun x => h x ^ 4) := by
  norm_num [expect] at *
  have h_cauchy_schwarz :
      (∑ x, g x ^ 2 * h x ^ 2) ^ 2 ≤ (∑ x, g x ^ 4) * (∑ x, h x ^ 4) := by
    have h_cs : ∀ u v : BoolCube n → ℝ,
        (∑ x, u x * v x) ^ 2 ≤ (∑ x, u x ^ 2) * (∑ x, v x ^ 2) :=
      fun u v => Finset.sum_mul_sq_le_sq_mul_sq Finset.univ u v
    convert h_cs (fun x => g x ^ 2) (fun x => h x ^ 2) using 3 <;> ring
  nlinarith [show 0 ≤ uniformWeight n ^ 2 by positivity]

/-- Expectations of squares are nonnegative. -/
lemma expect_sq_nonneg {n : ℕ} (f : BooleanFunc n) :
    0 ≤ expect (fun x => f x ^ 2) := by
  exact mul_nonneg (pow_nonneg (by norm_num) _)
    (Finset.sum_nonneg fun _ _ => sq_nonneg _)

/-- Expectations of products of squares are nonnegative. -/
lemma expect_sq_nonneg_prod {n : ℕ} (g h : BooleanFunc n) :
    0 ≤ expect (fun x => g x ^ 2 * h x ^ 2) := by
  exact mul_nonneg (pow_nonneg (by norm_num) _)
    (Finset.sum_nonneg fun _ _ => by positivity)

/-- Expectations of fourth powers are nonnegative. -/
lemma expect_fourth_nonneg {n : ℕ} (f : BooleanFunc n) :
    0 ≤ expect (fun x => f x ^ 4) := by
  convert expect_sq_nonneg_prod (fun x => f x ^ 2) (fun _ => 1) using 1
  norm_num [sq]
  ring_nf

/-- Averaging over the last coordinate preserves a Fourier degree bound. -/
lemma degree_avgLast {n : ℕ} (f : BooleanFunc (n + 1)) (k : ℕ)
    (hf : has_degree_at_most f k) :
    has_degree_at_most (avgLast f) k := by
  intro S hS_nonzero
  have h_fourier_coeff :
      BooleanAnalysis.fourierCoeff (avgLast f) S =
        BooleanAnalysis.fourierCoeff f (S.image Fin.castSucc) := by
    unfold BooleanAnalysis.fourierCoeff avgLast
    unfold innerProduct restrictLast
    unfold expect
    have h_expand :
        ∑ x : BoolCube (n + 1), f x * chiS (Finset.image Fin.castSucc S) x =
          ∑ x : BoolCube n,
            (f (Fin.snoc x false) * chiS (Finset.image Fin.castSucc S) (Fin.snoc x false) +
             f (Fin.snoc x true) * chiS (Finset.image Fin.castSucc S) (Fin.snoc x true)) := by
      convert sum_boolCube_succ _
      rw [Finset.sum_add_distrib]
    simp_all +decide [Finset.sum_add_distrib, add_mul, mul_add, div_mul_eq_mul_div,
      Finset.mul_sum _ _ _]
    rw [← Finset.sum_add_distrib]
    refine' Finset.sum_congr rfl fun x hx => _
    unfold uniformWeight
    ring_nf
    unfold chiS
    simp +decide [Finset.prod_image]
    ring
  have := hf (Finset.image Fin.castSucc S)
  simp_all +decide [Finset.card_image_of_injective, Function.Injective]

/-- Taking the half-difference over the last coordinate lowers a Fourier degree bound by one. -/
lemma degree_diffLast {n : ℕ} (f : BooleanFunc (n + 1)) (k : ℕ)
    (hf : has_degree_at_most f k) :
    has_degree_at_most (diffLast f) (k - 1) := by
  have h_fourier_coeff : ∀ S : Finset (Fin n),
      BooleanAnalysis.fourierCoeff (diffLast f) S =
        BooleanAnalysis.fourierCoeff f (Finset.image Fin.castSucc S ∪ {Fin.last n}) := by
    exact fourierCoeff_diffLast f
  intro S hS_nonzero
  have h_card : S.card + 1 ≤ k := by
    have := hf (Finset.image Fin.castSucc S ∪ {Fin.last n})
    simp_all +decide [Finset.card_image_of_injective, Function.Injective]
  exact Nat.le_sub_one_of_lt h_card

end Bonami
