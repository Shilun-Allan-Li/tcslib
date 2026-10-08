/-
Copyright (c) 2026 TCSlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Owen McGinty
-/

import TCSlib.BooleanAnalysis.Hypercontractivity.Cube.Decomposition
import TCSlib.BooleanAnalysis.Hypercontractivity.Cube.EvenMoments
import TCSlib.BooleanAnalysis.Hypercontractivity.Cube.OneBit

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Noise kernels and coordinate identities

This is one stage of the forward hypercontractivity proof on the uniform Boolean cube.

## Main definitions

* `noiseKernel`: the coordinate-product transition kernel for cube noise.

## Main results

* `noiseKernel_nonneg`.
* `sum_fourier_kernel`.
* `noiseOp_eq_kernel_sum`.
* `innerProduct_noiseOp_eq_weighted_sum`.
* `corrExpect_mono`.
* `noiseKernel_snoc`.
* `expect_succ_eq_iterated`.
* `norm_collapse_rpow`.
* `weighted_sum_succ_decomp`.
* `one_bit_slice_eq_innerProduct`.
* `one_bit_norm_slice`.
* `norm_collapse_clean`.

## References

* [OD14] Ryan O'Donnell, *Analysis of Boolean Functions*, Cambridge University Press,
  2014, §§9.3–10.1.
-/

open BooleanAnalysis MeasureTheory Set Filter ProbabilityTheory Real
open scoped BigOperators ENNReal Classical

namespace BooleanAnalysis.Hypercontractivity

variable {n : ℕ}

/-! ## Noise Kernel -/

/-- The noise kernel is `K_ρ(x, y) = ∏_i ((1 + ρ · sign(x_i) · sign(y_i)) / 2)`.
For `|ρ| ≤ 1` it is the transition probability from `x` to `y` under correlated noise.
The formula extends polynomially to every real `ρ`; outside that interval its values
need not be probabilities.

**Source:** [OD14, Rem. 9.20 (product-space calculation)]. -/
noncomputable def noiseKernel (ρ : ℝ) {n : ℕ} (x y : BoolCube n) : ℝ :=
  ∏ i : Fin n, (1 + ρ * boolToSign (x i) * boolToSign (y i)) / 2

/-- Shows that the noise kernel is nonnegative for a valid noise parameter.

**Source:** [OD14, Rem. 9.20 (product-space calculation)]. -/
lemma noiseKernel_nonneg {ρ : ℝ} (hρ0 : 0 ≤ ρ) (hρ1 : ρ ≤ 1)
    (x y : BoolCube n) : 0 ≤ noiseKernel ρ x y := by
  refine Finset.prod_nonneg fun i _ ↦ ?_
  cases x i <;> cases y i <;> norm_num [boolToSign] <;> nlinarith
/-! ## Noise Operator as Kernel Sum -/

/-- Expands the product form of the noise kernel as a Fourier-character sum.

**Source:** [OD14, Rem. 9.20 (product-space calculation)]. -/
lemma sum_fourier_kernel (ρ : ℝ) (x y : BoolCube n) :
    ∑ S : Finset (Fin n), ρ ^ S.card * chiS S x * chiS S y =
    ∏ i : Fin n, (1 + ρ * boolToSign (x i) * boolToSign (y i)) := by
  have h_prod_sum : ∏ i : Fin n, (1 + ρ * boolToSign (x i) * boolToSign (y i)) =
      ∑ S : Finset (Fin n), ∏ i ∈ S, (ρ * boolToSign (x i) * boolToSign (y i)) := by
    simp +decide [add_comm, Finset.prod_add]
  rw [h_prod_sum, Finset.sum_congr rfl]
  intros; simp_all +decide [Finset.prod_mul_distrib, chiS]

/-- The noise operator equals a kernel sum: `T_ρ g(x) = ∑_y K_ρ(x,y) · g(y)`.

**Source:** [OD14, Rem. 9.20 (product-space calculation)]. -/
lemma noiseOp_eq_kernel_sum (ρ : ℝ) (g : BooleanFunc n) (x : BoolCube n) :
    noiseOp ρ g x = ∑ y : BoolCube n, noiseKernel ρ x y * g y := by
  unfold noiseOp noiseKernel BooleanAnalysis.fourierCoeff BooleanAnalysis.innerProduct
  simp +decide [BooleanAnalysis.expect]
  unfold uniformWeight
  simp +decide [div_eq_inv_mul, Finset.mul_sum, mul_assoc, mul_comm, mul_left_comm]
  rw [Finset.sum_comm, Finset.sum_congr rfl]; intros; ring_nf
  rw [← sum_fourier_kernel]
  simp +decide [mul_assoc, mul_comm, mul_left_comm, Finset.mul_sum]

/-! ## Inner Product as Kernel-Weighted Sum -/

/-- `⟨f, T_ρ g⟩ = (1/2^n) ∑_{x,y} K_ρ(x,y) · f(x) · g(y)`.
**Source:** [OD14, Rem. 9.20 (proof)]. -/
lemma innerProduct_noiseOp_eq_weighted_sum (ρ : ℝ) (f g : BooleanFunc n) :
    innerProduct f (noiseOp ρ g) =
    uniformWeight n * ∑ x : BoolCube n, ∑ y : BoolCube n,
      noiseKernel ρ x y * f x * g y := (by
  unfold innerProduct
  simp +decide [mul_assoc, Finset.mul_sum, expect]
  rw [Finset.sum_congr rfl fun _ _ => ?_]
  rw [noiseOp_eq_kernel_sum]
  simp +decide [mul_assoc, mul_comm, mul_left_comm, Finset.mul_sum]
)


/-! ## Correlated Monotonicity -/

/-- If `h(x,y) ≤ h'(x,y)` pointwise and `0 ≤ ρ ≤ 1`, then the kernel-weighted
expectation of `h` is at most that of `h'`.
**Source:** [OD14, Rem. 9.20 (proof)]. -/
lemma corrExpect_mono {ρ : ℝ} (hρ0 : 0 ≤ ρ) (hρ1 : ρ ≤ 1)
    {h h' : BoolCube n → BoolCube n → ℝ} (hle : ∀ x y, h x y ≤ h' x y) :
    uniformWeight n * ∑ x : BoolCube n, ∑ y : BoolCube n,
      noiseKernel ρ x y * h x y ≤
    uniformWeight n * ∑ x : BoolCube n, ∑ y : BoolCube n,
      noiseKernel ρ x y * h' x y := by
  apply_rules [mul_le_mul_of_nonneg_left, Finset.sum_le_sum]
  · exact fun x _ => Finset.sum_le_sum fun y _ =>
      mul_le_mul_of_nonneg_left (hle x y) (noiseKernel_nonneg hρ0 hρ1 x y)
  · exact pow_nonneg (by norm_num) _

/-! ## Noise Kernel Factorization -/

/-- The noise kernel on `BoolCube (n+1)` factors along the last coordinate.
**Source:** [OD14, Rem. 9.20 (proof)]. -/
lemma noiseKernel_snoc (ρ : ℝ) (x' y' : BoolCube n) (b b' : Bool) :
    noiseKernel ρ (Fin.snoc x' b) (Fin.snoc y' b') =
    noiseKernel ρ x' y' * ((1 + ρ * boolToSign b * boolToSign b') / 2) := by
  unfold noiseKernel; simp +decide [Fin.prod_univ_castSucc]; ring

/-! ## Expectation Decomposition (Fubini for BoolCube) -/

/-- Rewrites an `(n + 1)`-cube expectation as an iterated expectation over its final coordinate.

**Source:** [OD14, Rem. 9.20 (proof)]. -/
lemma expect_succ_eq_iterated (h : BooleanFunc (n + 1)) :
    expect h = expect (fun x' =>
      (1/2 : ℝ) * (h (Fin.snoc x' false) + h (Fin.snoc x' true))) := by
  unfold expect
  rw [sum_boolCube_succ]
  norm_num [Finset.mul_sum, mul_add, mul_assoc, mul_left_comm,
            Finset.sum_add_distrib, uniformWeight_succ]
  ring_nf

/-! ## Norm Collapse (Fubini) -/

/-- Collapses an iterated `L^p` moment on an `(n + 1)`-cube to the global moment.

**Source:** [OD14, Rem. 9.20 (proof)]. -/
lemma norm_collapse_rpow (p : ℝ) (_hp : 0 < p) (f : BooleanFunc (n + 1)) :
    expect (fun x => |f x| ^ p) =
    expect (fun x' => (1/2 : ℝ) *
      (|f (Fin.snoc x' false)| ^ p + |f (Fin.snoc x' true)| ^ p)) := by
  convert expect_succ_eq_iterated _ using 1

/-! ## Decomposition of Weighted Sum at Dimension n+1 -/

/--
The kernel-weighted bilinear sum at dimension `n+1` decomposes by factoring the
kernel along the last coordinate.
**Source:** [OD14, Rem. 9.20 (proof)]. -/
lemma weighted_sum_succ_decomp (ρ : ℝ) (F : BoolCube (n + 1) → BoolCube (n + 1) → ℝ) :
    uniformWeight (n + 1) * ∑ x : BoolCube (n + 1), ∑ y : BoolCube (n + 1),
      noiseKernel ρ x y * F x y =
    uniformWeight n * ∑ x' : BoolCube n, ∑ y' : BoolCube n,
      noiseKernel ρ x' y' *
      ((1/2 : ℝ) * ∑ b : Bool, ∑ b' : Bool,
        ((1 + ρ * boolToSign b * boolToSign b') / 2) *
        F (Fin.snoc x' b) (Fin.snoc y' b')) := by
  convert congr_arg _ ( sum_boolCube_succ fun y => ∑ x, noiseKernel ρ y x * F y x ) using 1 ; norm_num ; ring_nf!;
  rw [ add_comm 1, uniformWeight_succ ] ; simp +decide [ Finset.sum_add_distrib, mul_assoc, mul_left_comm, mul_add, Finset.sum_add_distrib, mul_assoc, mul_left_comm,
    mul_add, Finset.sum_add_distrib, mul_assoc, mul_left_comm, mul_add, Finset.sum_add_distrib, Finset.mul_sum _ _ _, mul_assoc, mul_left_comm, mul_add] ; ring_nf;
  simp +decide only [← Finset.sum_add_distrib] ; ring_nf;
  refine' Finset.sum_congr rfl fun x _ => _ ; rw [ sum_boolCube_succ ] ; ring_nf;
  rw [ ← Finset.sum_add_distrib ] ; congr ; ext y ; rw [ noiseKernel_snoc, noiseKernel_snoc ] ; ring_nf;
  rw [ noiseKernel_snoc, noiseKernel_snoc ] ; norm_num [ boolToSign ] ; ring;

/-! ## One-Bit Correlated Expectation as Inner Product -/

/--
For fixed `x'` and `y'`, the one-bit kernel-weighted sum of the slices of `f` and `g`
equals the one-bit inner product with noise operator.
**Source:** [OD14, Rem. 9.20 (proof)]. -/
lemma one_bit_slice_eq_innerProduct (ρ : ℝ) (f g : BooleanFunc (n + 1))
    (x' y' : BoolCube n) :
    (1/2 : ℝ) * ∑ b : Bool, ∑ b' : Bool,
      ((1 + ρ * boolToSign b * boolToSign b') / 2) *
      f (Fin.snoc x' b) * g (Fin.snoc y' b') =
    innerProduct (fun t : BoolCube 1 => f (Fin.snoc x' (t 0)))
                 (noiseOp ρ (fun t : BoolCube 1 => g (Fin.snoc y' (t 0)))) := by
  unfold BooleanAnalysis.noiseOp;
  unfold BooleanAnalysis.innerProduct BooleanAnalysis.fourierCoeff
  simp;
  rw [ show ( Finset.univ : Finset ( Finset ( Fin 1 ) ) ) = { ∅, { 0 } } by decide ] ; norm_num ; ring_nf;
  unfold BooleanAnalysis.expect; norm_num [ Finset.sum_range_succ, Finset.sum_range_zero, BooleanAnalysis.innerProduct ] ; ring_nf;
  unfold BooleanAnalysis.expect; norm_num [ Finset.sum_range_succ, Finset.sum_range_zero, BooleanAnalysis.uniformWeight ] ; ring_nf;
  rw [ show ( Finset.univ : Finset ( BoolCube 1 ) ) = { fun _ => false, fun _ => true } by decide ] ; norm_num ; ring_nf;
  rw [ Finset.sum_pair, Finset.sum_pair ] <;> norm_num [ boolToSign ] ; ring_nf;
  · grind +splitImp;
  · exact fun h => by have := congr_fun h 0; simp +decide at this;
  · exact fun h => by have := congr_fun h 0; simp +decide at this;

/-! ## One-bit Lp norm of slices -/
/--
The one-bit `L^p` norm of the slice `t ↦ f(snoc x' (t 0))`.
**Source:** [OD14, Rem. 9.20 (proof)]. -/
lemma one_bit_norm_slice (p : ℝ) (_hp : 0 < p) (f : BooleanFunc (n + 1)) (x' : BoolCube n) :
    (expect (fun t : BoolCube 1 => |f (Fin.snoc x' (t 0))| ^ p)) ^ (1/p) =
    ((|f (Fin.snoc x' false)| ^ p + |f (Fin.snoc x' true)| ^ p) / 2) ^ (1/p) := by
  unfold expect;
  unfold uniformWeight; norm_num [ Finset.card_univ ] ; ring_nf;
  rw [ show ( Finset.univ : Finset ( Fin 1 → Bool ) ) = { fun _ => Bool.false, fun _ => Bool.true } by decide, Finset.sum_pair ] <;> norm_num ; ring_nf;
  decide +revert

/-! ## Norm Collapse (clean form) -/
/-
The iterated norm collapses: `E_{x'}[F(x')^p] = E_x[|f(x)|^p]` where
`F(x') = (E_t[|f(x',t)|^p])^{1/p}`.
-/
/-- Gives the clean iterated-norm identity used in the product-space induction.

**Source:** [OD14, Rem. 9.20 (proof)]. -/
lemma norm_collapse_clean (p : ℝ) (hp : 1 ≤ p) (f : BooleanFunc (n + 1)) :
    expect (fun x' =>
      ((|f (Fin.snoc x' false)| ^ p + |f (Fin.snoc x' true)| ^ p) / 2) ) =
    expect (fun x => |f x| ^ p) := by
  convert norm_collapse_rpow p ( by linarith ) f |> Eq.symm using 2;
  exact funext fun x' => by ring;

end BooleanAnalysis.Hypercontractivity
