import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Analysis.Normed.Ring.Lemmas
import Mathlib.Data.Int.Star
import Mathlib.Tactic
import Mathlib
import Mathlib.Tactic.Cases
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
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.Fin.Basic

namespace BooleanAnalysis
end BooleanAnalysis

set_option maxHeartbeats 400000

open scoped BigOperators

namespace BooleanAnalysis
abbrev BoolCube (n : ℕ) := Fin n → Bool
end BooleanAnalysis

namespace BooleanAnalysis
abbrev BooleanFunc (n : ℕ) := BoolCube n → ℝ
end BooleanAnalysis

namespace BooleanAnalysis
variable {n : ℕ}
noncomputable def uniformWeight (n : ℕ) : ℝ := (2 : ℝ)⁻¹ ^ n
end BooleanAnalysis

namespace BooleanAnalysis
variable {n : ℕ}
noncomputable def expect (f : BooleanFunc n) : ℝ :=
  uniformWeight n * ∑ x : BoolCube n, f x
end BooleanAnalysis

namespace BooleanAnalysis
variable {n : ℕ}
noncomputable def innerProduct (f g : BooleanFunc n) : ℝ :=
  expect (fun x ↦ f x * g x)
end BooleanAnalysis

namespace BooleanAnalysis
variable {n : ℕ}
def boolToSign (b : Bool) : ℝ := if b then -1 else 1
end BooleanAnalysis

namespace BooleanAnalysis
variable {n : ℕ}
@[simp]
lemma boolToSign_mul_self (b : Bool) : boolToSign b * boolToSign b = 1 := by
  cases b <;> simp [boolToSign]
end BooleanAnalysis

namespace BooleanAnalysis
variable {n : ℕ}
noncomputable def chiS (S : Finset (Fin n)) : BooleanFunc n :=
  fun x ↦ ∏ i ∈ S, boolToSign (x i)
end BooleanAnalysis

namespace BooleanAnalysis
variable {n : ℕ}
noncomputable def fourierCoeff (f : BooleanFunc n) (S : Finset (Fin n)) : ℝ :=
  innerProduct f (chiS S)
end BooleanAnalysis

namespace BooleanAnalysis
variable {n : ℕ}
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
end BooleanAnalysis

namespace BooleanAnalysis
variable {n : ℕ}
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
end BooleanAnalysis

namespace BooleanAnalysis
variable {n : ℕ}
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
end BooleanAnalysis

namespace BooleanAnalysis
variable {n : ℕ}
def isOddFunc (f : BooleanFunc n) : Prop :=
  ∀ x : BoolCube n, f (fun i => !x i) = -f x
end BooleanAnalysis

namespace BooleanAnalysis
variable {n : ℕ}
def isPmOne (f : BooleanFunc n) : Prop :=
  ∀ x : BoolCube n, f x = 1 ∨ f x = -1
end BooleanAnalysis

set_option maxHeartbeats 800000

open scoped BigOperators

open BooleanAnalysis

namespace ArrowTheorem
variable {n : ℕ}
def abPref : Fin 6 → Bool
  | ⟨0, _⟩ => false  -- a > b > c
  | ⟨1, _⟩ => false  -- a > c > b
  | ⟨2, _⟩ => true   -- b > a > c
  | ⟨3, _⟩ => true   -- b > c > a
  | ⟨4, _⟩ => false  -- c > a > b
  | ⟨5, _⟩ => true   -- c > b > a
end ArrowTheorem

namespace ArrowTheorem
variable {n : ℕ}
def bcPref : Fin 6 → Bool
  | ⟨0, _⟩ => false  -- a > b > c
  | ⟨1, _⟩ => true   -- a > c > b
  | ⟨2, _⟩ => false  -- b > a > c
  | ⟨3, _⟩ => false  -- b > c > a
  | ⟨4, _⟩ => true   -- c > a > b
  | ⟨5, _⟩ => true   -- c > b > a
end ArrowTheorem

namespace ArrowTheorem
variable {n : ℕ}
def caPref : Fin 6 → Bool
  | ⟨0, _⟩ => true   -- a > b > c: prefer a, so in ca: prefer a = true
  | ⟨1, _⟩ => true   -- a > c > b
  | ⟨2, _⟩ => true   -- b > a > c
  | ⟨3, _⟩ => false  -- b > c > a: prefer c
  | ⟨4, _⟩ => false  -- c > a > b: prefer c
  | ⟨5, _⟩ => false  -- c > b > a: prefer c
end ArrowTheorem

namespace ArrowTheorem
variable {n : ℕ}
lemma sum_abPref_bcPref :
    ∑ k : Fin 6, boolToSign (abPref k) * boolToSign (bcPref k) = -2 := by
  simp only [Fin.sum_univ_six, abPref, bcPref, boolToSign]
  norm_num
end ArrowTheorem

namespace ArrowTheorem
variable {n : ℕ}
lemma sum_bcPref_caPref :
    ∑ k : Fin 6, boolToSign (bcPref k) * boolToSign (caPref k) = -2 := by
  simp only [Fin.sum_univ_six, bcPref, caPref, boolToSign]
  norm_num
end ArrowTheorem

namespace ArrowTheorem
variable {n : ℕ}
lemma sum_abPref_caPref :
    ∑ k : Fin 6, boolToSign (abPref k) * boolToSign (caPref k) = -2 := by
  simp only [Fin.sum_univ_six, abPref, caPref, boolToSign]
  norm_num
end ArrowTheorem

namespace ArrowTheorem
variable {n : ℕ}
abbrev Profile (n : ℕ) := Fin n → Fin 6
end ArrowTheorem

namespace ArrowTheorem
variable {n : ℕ}
def abVotes (p : Profile n) : BoolCube n := fun i => abPref (p i)
end ArrowTheorem

namespace ArrowTheorem
variable {n : ℕ}
def bcVotes (p : Profile n) : BoolCube n := fun i => bcPref (p i)
end ArrowTheorem

namespace ArrowTheorem
variable {n : ℕ}
def caVotes (p : Profile n) : BoolCube n := fun i => caPref (p i)
end ArrowTheorem

namespace ArrowTheorem
variable {n : ℕ}
def acyclic (f : BooleanFunc n) : Prop :=
  ∀ p : Profile n,
    ¬ (f (abVotes p) = 1 ∧ f (bcVotes p) = 1 ∧ f (caVotes p) = 1) ∧
    ¬ (f (abVotes p) = -1 ∧ f (bcVotes p) = -1 ∧ f (caVotes p) = -1)
end ArrowTheorem

namespace ArrowTheorem
variable {n : ℕ}
noncomputable def corrFunc (f : BooleanFunc n) : ℝ :=
  ∑ S : Finset (Fin n), fourierCoeff f S ^ 2 * (-1/3 : ℝ) ^ S.card
end ArrowTheorem

namespace ArrowTheorem
variable {n : ℕ}
private lemma sum_abPref_sign :
    ∑ k : Fin 6, boolToSign (abPref k) = 0 := by
  simp only [Fin.sum_univ_six, abPref, boolToSign]
  norm_num
end ArrowTheorem

namespace ArrowTheorem
variable {n : ℕ}
private lemma sum_bcPref_sign :
    ∑ k : Fin 6, boolToSign (bcPref k) = 0 := by
  simp only [Fin.sum_univ_six, bcPref, boolToSign]
  norm_num
end ArrowTheorem

namespace ArrowTheorem
variable {n : ℕ}
private lemma sum_caPref_sign :
    ∑ k : Fin 6, boolToSign (caPref k) = 0 := by
  simp only [Fin.sum_univ_six, caPref, boolToSign]
  norm_num
end ArrowTheorem

namespace ArrowTheorem
variable {n : ℕ}
private lemma prod_finset_eq_prod_univ_ite {n : ℕ} (A : Finset (Fin n)) (g : Fin n → ℝ) :
    ∏ j ∈ A, g j = ∏ j : Fin n, if j ∈ A then g j else 1 := by
  rw [← Finset.prod_filter]; congr 1; simp
end ArrowTheorem

namespace ArrowTheorem
variable {n : ℕ}
private lemma profile_kernel_gen {xPref yPref : Fin 6 → Bool}
    (hx : ∑ k : Fin 6, boolToSign (xPref k) = 0)
    (hy : ∑ k : Fin 6, boolToSign (yPref k) = 0)
    (hxy : ∑ k : Fin 6, boolToSign (xPref k) * boolToSign (yPref k) = -2)
    (S T : Finset (Fin n)) :
    (1/6 : ℝ)^n * ∑ p : Profile n,
      chiS S (fun i => xPref (p i)) * chiS T (fun i => yPref (p i)) =
    if S = T then (-1/3 : ℝ)^S.card else 0 := by
  simp only [chiS]
  simp_rw [prod_finset_eq_prod_univ_ite S, prod_finset_eq_prod_univ_ite T,
           ← Finset.prod_mul_distrib]
  rw [show ∑ p : Profile n, ∏ i : Fin n,
        ((if i ∈ S then boolToSign (xPref (p i)) else 1) *
         (if i ∈ T then boolToSign (yPref (p i)) else 1)) =
        ∏ i : Fin n, ∑ k : Fin 6,
        ((if i ∈ S then boolToSign (xPref k) else 1) *
         (if i ∈ T then boolToSign (yPref k) else 1)) from
    (Fintype.prod_sum (fun i (k : Fin 6) =>
       (if i ∈ S then boolToSign (xPref k) else 1) *
       (if i ∈ T then boolToSign (yPref k) else 1))).symm]
  have per_voter : ∀ i : Fin n,
      ∑ k : Fin 6, (if i ∈ S then boolToSign (xPref k) else 1) *
                   (if i ∈ T then boolToSign (yPref k) else 1) =
      if i ∈ S then (if i ∈ T then (-2 : ℝ) else 0) else (if i ∈ T then 0 else 6) := by
    intro i
    by_cases hiS : i ∈ S <;> by_cases hiT : i ∈ T
    · simp only [if_pos hiS, if_pos hiT]; exact hxy
    · simp only [if_pos hiS, if_neg hiT, mul_one]; simpa using hx
    · simp only [if_neg hiS, if_pos hiT, one_mul]; simpa using hy
    · simp only [if_neg hiS, if_neg hiT, mul_one]; norm_num [Fin.sum_univ_six]
  simp_rw [per_voter]
  by_cases hST : S = T
  · subst hST
    simp only [if_true]
    simp_rw [show ∀ i : Fin n,
        (if i ∈ S then (if i ∈ S then (-2:ℝ) else 0) else (if i ∈ S then 0 else 6)) =
        if i ∈ S then (-2:ℝ) else 6 from fun i => by by_cases hi : i ∈ S <;> simp [hi]]
    simp_rw [show ∀ i : Fin n,
        (if i ∈ S then (-2:ℝ) else 6) = 6 * (if i ∈ S then (-1/3:ℝ) else 1) from
      fun i => by by_cases hi : i ∈ S; simp [hi]; norm_num; simp [hi]]
    rw [Finset.prod_mul_distrib]
    have h6 : ∏ _i : Fin n, (6 : ℝ) = 6 ^ n := by
      simp [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
    have prod_ite : ∏ i : Fin n, (if i ∈ S then (-1/3 : ℝ) else 1) = (-1/3 : ℝ) ^ S.card := by
      rw [← Finset.prod_filter, show Finset.univ.filter (· ∈ S) = S from by simp,
          Finset.prod_const]
    rw [h6, prod_ite]
    rw [← mul_assoc, ← mul_pow, show (1/6 : ℝ) * 6 = 1 from by norm_num, one_pow, one_mul]
  · simp only [if_neg hST]
    have hne : symmDiff S T ≠ ∅ := by
      intro h
      apply hST
      have : symmDiff S T = ⊥ := by rwa [Finset.bot_eq_empty]
      exact symmDiff_eq_bot.mp this
    obtain ⟨i, hi⟩ := Finset.nonempty_iff_ne_empty.mpr hne
    rw [Finset.mem_symmDiff] at hi
    rw [mul_eq_zero]
    right
    apply Finset.prod_eq_zero (Finset.mem_univ i)
    rcases hi with ⟨hiS, hiT⟩ | ⟨hiT, hiS⟩
    · simp only [if_pos hiS, if_neg hiT]
    · simp only [if_neg hiS, if_pos hiT]
end ArrowTheorem

namespace ArrowTheorem
variable {n : ℕ}
private lemma profile_inner_product_kernel (S T : Finset (Fin n)) :
    (1/6 : ℝ)^n * ∑ p : Profile n,
      chiS S (abVotes p) * chiS T (bcVotes p) =
    if S = T then (-1/3 : ℝ)^S.card else 0 :=
  profile_kernel_gen sum_abPref_sign sum_bcPref_sign sum_abPref_bcPref S T
end ArrowTheorem

namespace ArrowTheorem
variable {n : ℕ}
private lemma profile_kernel_bcca (S T : Finset (Fin n)) :
    (1/6 : ℝ)^n * ∑ p : Profile n,
      chiS S (bcVotes p) * chiS T (caVotes p) =
    if S = T then (-1/3 : ℝ)^S.card else 0 :=
  profile_kernel_gen sum_bcPref_sign sum_caPref_sign sum_bcPref_caPref S T
end ArrowTheorem

namespace ArrowTheorem
variable {n : ℕ}
private lemma profile_kernel_abca (S T : Finset (Fin n)) :
    (1/6 : ℝ)^n * ∑ p : Profile n,
      chiS S (abVotes p) * chiS T (caVotes p) =
    if S = T then (-1/3 : ℝ)^S.card else 0 :=
  profile_kernel_gen sum_abPref_sign sum_caPref_sign sum_abPref_caPref S T
end ArrowTheorem

namespace ArrowTheorem
variable {n : ℕ}
private lemma expected_product_helper (f : BooleanFunc n)
    (votes1 votes2 : Profile n → BoolCube n)
    (hkernel : ∀ S T : Finset (Fin n),
      (1/6 : ℝ)^n * ∑ p : Profile n, chiS S (votes1 p) * chiS T (votes2 p) =
      if S = T then (-1/3 : ℝ)^S.card else 0) :
    (1/6 : ℝ)^n * ∑ p : Profile n, f (votes1 p) * f (votes2 p) = corrFunc f := by
  simp only [corrFunc]
  simp_rw [show ∀ p : Profile n, f (votes1 p) =
      ∑ S : Finset (Fin n), fourierCoeff f S * chiS S (votes1 p) from
    fun p => walsh_expansion f (votes1 p),
    show ∀ p : Profile n, f (votes2 p) =
      ∑ T : Finset (Fin n), fourierCoeff f T * chiS T (votes2 p) from
    fun p => walsh_expansion f (votes2 p)]
  -- Expand product of sums, keeping S as outer variable
  simp_rw [show ∀ p : Profile n,
      (∑ S : Finset (Fin n), fourierCoeff f S * chiS S (votes1 p)) *
      (∑ T : Finset (Fin n), fourierCoeff f T * chiS T (votes2 p)) =
      ∑ S : Finset (Fin n), ∑ T : Finset (Fin n),
        (fourierCoeff f S * chiS S (votes1 p)) * (fourierCoeff f T * chiS T (votes2 p)) from
    fun p => by
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl; intro S _
      rw [Finset.mul_sum]]
  -- Distribute (1/6)^n inside: ∑_p ∑_S ∑_T (fS*xS)*(fT*yT) → ∑_p ∑_S ∑_T (1/6)^n*(...)
  rw [Finset.mul_sum]
  simp_rw [Finset.mul_sum]
  -- Swap ∑_p ↔ ∑_S
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl; intro S _
  -- Swap ∑_p ↔ ∑_T
  rw [Finset.sum_comm]
  -- Convert each (S,T)-block using the kernel
  trans (∑ T : Finset (Fin n), fourierCoeff f S * fourierCoeff f T *
      ((1/6 : ℝ)^n * ∑ p : Profile n, chiS S (votes1 p) * chiS T (votes2 p)))
  · apply Finset.sum_congr rfl; intro T _
    rw [← Finset.mul_sum]
    have hsumeq : ∑ p : Profile n,
          (fourierCoeff f S * chiS S (votes1 p)) * (fourierCoeff f T * chiS T (votes2 p)) =
        fourierCoeff f S * fourierCoeff f T *
          ∑ p : Profile n, chiS S (votes1 p) * chiS T (votes2 p) := by
      rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro p _; ring
    rw [hsumeq]; ring
  · -- Apply the kernel then collapse the diagonal sum
    simp_rw [hkernel]
    simp only [mul_ite, mul_zero]
    rw [Finset.sum_ite_eq, if_pos (Finset.mem_univ _)]
    ring
end ArrowTheorem

namespace ArrowTheorem
variable {n : ℕ}
lemma expected_product_eq_corrFunc (f : BooleanFunc n) :
    (1/6 : ℝ)^n * ∑ p : Profile n, f (abVotes p) * f (bcVotes p) = corrFunc f :=
  expected_product_helper f abVotes bcVotes profile_inner_product_kernel
end ArrowTheorem

namespace ArrowTheorem
variable {n : ℕ}
private lemma expected_product_bcca (f : BooleanFunc n) :
    (1/6 : ℝ)^n * ∑ p : Profile n, f (bcVotes p) * f (caVotes p) = corrFunc f :=
  expected_product_helper f bcVotes caVotes profile_kernel_bcca
end ArrowTheorem

namespace ArrowTheorem
variable {n : ℕ}
private lemma expected_product_abca (f : BooleanFunc n) :
    (1/6 : ℝ)^n * ∑ p : Profile n, f (abVotes p) * f (caVotes p) = corrFunc f :=
  expected_product_helper f abVotes caVotes profile_kernel_abca
end ArrowTheorem

namespace ArrowTheorem
variable {n : ℕ}
lemma acyclic_implies_corrFunc (f : BooleanFunc n) (_hodd : isOddFunc f) (hpm : isPmOne f)
    (hacyc : acyclic f) : corrFunc f = -1/3 := by
  -- Step 1: per-profile, the three products sum to -1
  have hprod : ∀ p : Profile n,
      f (abVotes p) * f (bcVotes p) +
      f (bcVotes p) * f (caVotes p) +
      f (abVotes p) * f (caVotes p) = -1 := by
    intro p
    obtain ⟨hcyc1, hcyc2⟩ := hacyc p
    rcases hpm (abVotes p) with ha | ha <;>
    rcases hpm (bcVotes p) with hb | hb <;>
    rcases hpm (caVotes p) with hc | hc
    · exact absurd ⟨ha, hb, hc⟩ hcyc1
    · rw [ha, hb, hc]; norm_num
    · rw [ha, hb, hc]; norm_num
    · rw [ha, hb, hc]; norm_num
    · rw [ha, hb, hc]; norm_num
    · rw [ha, hb, hc]; norm_num
    · rw [ha, hb, hc]; norm_num
    · exact absurd ⟨ha, hb, hc⟩ hcyc2
  -- Step 2: (1/6)^n * ∑_p (sum of products) = 3 * corrFunc f
  have hkey : (1/6 : ℝ)^n * ∑ p : Profile n,
      (f (abVotes p) * f (bcVotes p) +
       f (bcVotes p) * f (caVotes p) +
       f (abVotes p) * f (caVotes p)) = 3 * corrFunc f := by
    simp_rw [Finset.sum_add_distrib]
    rw [mul_add, mul_add,
        expected_product_eq_corrFunc f,
        expected_product_bcca f,
        expected_product_abca f]
    ring
  -- Step 3: (1/6)^n * ∑_p (sum of products) = -1 (from hprod)
  have hval : (1/6 : ℝ)^n * ∑ p : Profile n,
      (f (abVotes p) * f (bcVotes p) +
       f (bcVotes p) * f (caVotes p) +
       f (abVotes p) * f (caVotes p)) = -1 := by
    simp_rw [hprod]
    have hn : Fintype.card (Profile n) = 6^n := by
      simp [Fintype.card_pi, Fintype.card_fin, Finset.prod_const, Finset.card_univ]
    rw [Finset.sum_const, Finset.card_univ, hn, nsmul_eq_mul]
    push_cast
    have h : (1 / 6 : ℝ) ^ n * (6 : ℝ) ^ n = 1 := by rw [← mul_pow]; norm_num
    linarith [mul_neg ((1 / 6 : ℝ) ^ n) ((6 : ℝ) ^ n)]
  -- Combine
  linarith
end ArrowTheorem
