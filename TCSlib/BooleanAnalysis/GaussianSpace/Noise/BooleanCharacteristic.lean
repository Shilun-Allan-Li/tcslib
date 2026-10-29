/-
Copyright (c) 2026 TCSlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TCSlib Contributors
-/

import TCSlib.BooleanAnalysis.GaussianSpace.Noise.BlockCharacteristic
import TCSlib.BooleanAnalysis.Hypercontractivity.Cube.General.Bounds

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Fourier expectations under Boolean noise

## Main definitions

The existing Boolean noise kernel and uniform cube weights are reused.

* `normalizedCubeBlocks`: the normalized sum in each block of cube coordinates.

## Main results

Finite coordinate factorization identifies the Fourier transform of Boolean
noise with products of the one-pair characteristic function.

## References

* [OD14] Ryan O'Donnell, *Analysis of Boolean Functions*, Cambridge University Press,
  2014; May 2021 arXiv edition, §11.1, BitsToGaussians and Gaussian Hypercontractivity.
-/

open MeasureTheory Filter
open scoped BigOperators Topology

namespace BooleanAnalysis.GaussianSpace

open Hypercontractivity

/-- Split cube coordinates into `n` blocks of size `m` and normalize every block
sum by `√m`. [OD14, §11.1, BitsToGaussians]
The formula is total also when a block is empty. -/
noncomputable def normalizedCubeBlocks (n m : ℕ) (x : BoolCube (n * m)) : Fin n → ℝ :=
  fun i => (∑ j : Fin m, boolToSign (x (finProdFinEquiv (i, j)))) / Real.sqrt m

/-- The double sum of a product of independent coordinate factors equals the
product of their four-entry Boolean sums. -/
lemma sum_pair_coordinate_products {ι : Type*} [Fintype ι] [DecidableEq ι]
    (H : ι → Bool → Bool → ℂ) :
    (∑ x : ι → Bool, ∑ y : ι → Bool, ∏ i, H i (x i) (y i)) =
      ∏ i, ∑ b : Bool, ∑ c : Bool, H i b c := by
  simp_rw [← Fintype.prod_sum]
  exact (Fintype.prod_sum (fun i b => ∑ c : Bool, H i b c)).symm

/-- The four-entry correlated Boolean kernel has the characteristic function
given by the equal-sign and opposite-sign cosine mixture.
[OD14, §11.1, BitsToGaussians]

**Proof sketch.** Expand the four Boolean pairs and group opposite exponential
phases using the complex cosine identity. -/
lemma sum_correlatedSign_phase (ρ a b : ℝ) :
    (∑ x : Bool, ∑ y : Bool,
      (1 + (ρ : ℂ) * (boolToSign x : ℂ) * (boolToSign y : ℂ)) / 4 *
        Complex.exp (((a * boolToSign x + b * boolToSign y : ℝ) : ℂ) * Complex.I)) =
      (correlatedSignCharacteristic ρ a b : ℂ) := by
  simp [boolToSign, correlatedSignCharacteristic,
    Complex.ofReal_cos, Complex.cos]
  ring_nf

/-- The Fourier transform of the Boolean noise coupling factors over coordinates.
[OD14, §11.1, BitsToGaussians]

**Proof sketch.** Factor the phase exponential and the product noise kernel.
Distribute the independent finite sums coordinatewise and apply the one-pair formula. -/
lemma sum_noiseKernel_phase {N : ℕ} (ρ : ℝ) (a b : Fin N → ℝ) :
    (uniformWeight N : ℂ) * (∑ x : BoolCube N, ∑ y : BoolCube N,
      (noiseKernel ρ x y : ℂ) * Complex.exp
        (((∑ i, (a i * boolToSign (x i) + b i * boolToSign (y i)) : ℝ) : ℂ) * Complex.I)) =
      ∏ i, (correlatedSignCharacteristic ρ (a i) (b i) : ℂ) := by
  classical
  let H (i : Fin N) (x y : Bool) : ℂ :=
    (1 + (ρ : ℂ) * (boolToSign x : ℂ) * (boolToSign y : ℂ)) / 4 *
      Complex.exp (((a i * boolToSign x + b i * boolToSign y : ℝ) : ℂ) * Complex.I)
  have hw : (uniformWeight N : ℂ) = ∏ _i : Fin N, (1 / 2 : ℂ) := by
    simp [uniformWeight, one_div]
  have he (x y : BoolCube N) :
      (uniformWeight N : ℂ) * ((noiseKernel ρ x y : ℂ) * Complex.exp
        (((∑ i, (a i * boolToSign (x i) + b i * boolToSign (y i)) : ℝ) : ℂ) * Complex.I)) =
        ∏ i, H i (x i) (y i) := by
    rw [hw]
    simp only [noiseKernel, Complex.ofReal_prod]
    rw [Complex.ofReal_sum, Finset.sum_mul, Complex.exp_sum,
      ← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib]
    apply Finset.prod_congr rfl
    intro i _
    dsimp [H]
    push_cast
    ring
  calc
    _ = ∑ x : BoolCube N, ∑ y : BoolCube N, ∏ i, H i (x i) (y i) := by
      rw [Finset.mul_sum]
      simp_rw [Finset.mul_sum, he]
    _ = ∏ i, ∑ x : Bool, ∑ y : Bool, H i x y := sum_pair_coordinate_products H
    _ = _ := by
      apply Finset.prod_congr rfl
      intro i _
      exact sum_correlatedSign_phase ρ (a i) (b i)

/-- A linear phase of normalized block sums is a linear phase of the underlying
bits, with each frequency divided by the square root of the block size. -/
lemma phase_normalizedCubeBlocks {n m : ℕ} (a b : Fin n → ℝ)
    (x y : BoolCube (n * m)) :
    (∑ i, (a i * normalizedCubeBlocks n m x i + b i * normalizedCubeBlocks n m y i)) =
      ∑ k : Fin (n * m),
        (a (finProdFinEquiv.symm k).1 / Real.sqrt m * boolToSign (x k) +
          b (finProdFinEquiv.symm k).1 / Real.sqrt m * boolToSign (y k)) := by
  rw [← finProdFinEquiv.sum_comp, Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro i _
  simp only [normalizedCubeBlocks, Equiv.symm_apply_apply]
  simp_rw [Finset.sum_div, Finset.mul_sum]
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro j _
  ring

/-- The joint phase expectation of normalized Boolean blocks is a product of
one-pair characteristic functions raised to the block size.
[OD14, §11.1, BitsToGaussians]

**Proof sketch.** Flatten the block phase into its bit frequencies and apply
coordinate factorization. Regroup identical frequencies in each block. -/
lemma sum_noiseKernel_normalizedCubeBlocks_phase {n m : ℕ} (ρ : ℝ) (a b : Fin n → ℝ) :
    (uniformWeight (n * m) : ℂ) * (∑ x : BoolCube (n * m), ∑ y : BoolCube (n * m),
      (noiseKernel ρ x y : ℂ) * Complex.exp
        (((∑ i, (a i * normalizedCubeBlocks n m x i +
          b i * normalizedCubeBlocks n m y i) : ℝ) : ℂ) * Complex.I)) =
      ∏ i, (correlatedSignCharacteristic ρ (a i / Real.sqrt m) (b i / Real.sqrt m) : ℂ) ^ m := by
  simp_rw [phase_normalizedCubeBlocks]
  rw [sum_noiseKernel_phase, ← finProdFinEquiv.prod_comp, Fintype.prod_prod_type]
  simp only [Equiv.symm_apply_apply, Finset.prod_const, Finset.card_univ, Fintype.card_fin]

/-- Fourier expectations of normalized correlated Boolean blocks converge to
the corresponding correlated Gaussian expectation.
[OD14, §11.1, BitsToGaussians]

**Proof sketch.** The finite kernel formula gives a product of characteristic
powers. Apply the scalar characteristic limit and identify the product with the
Gaussian covariance exponential. -/
lemma tendsto_sum_noiseKernel_normalizedCubeBlocks_phase {n : ℕ} {ρ : ℝ}
    (hρ : ρ ∈ Set.Icc (-1 : ℝ) 1) (a b : Fin n → ℝ) :
    Filter.Tendsto (fun m : ℕ => (uniformWeight (n * m) : ℂ) *
      (∑ x : BoolCube (n * m), ∑ y : BoolCube (n * m),
        (noiseKernel ρ x y : ℂ) * Complex.exp
          (((∑ i, (a i * normalizedCubeBlocks n m x i +
            b i * normalizedCubeBlocks n m y i) : ℝ) : ℂ) * Complex.I)))
      Filter.atTop (𝓝 (∫ z : (Fin n → ℝ) × (Fin n → ℝ),
        Complex.exp (((∑ i, (a i * z.1 i + b i * z.2 i) : ℝ) : ℂ) * Complex.I)
          ∂correlatedGaussianMeasure ρ)) := by
  have ht : Filter.Tendsto (fun m : ℕ =>
      ∏ i, (correlatedSignCharacteristic ρ (a i / Real.sqrt m) (b i / Real.sqrt m) : ℂ) ^ m)
      Filter.atTop (𝓝 (∏ i, (Real.exp (-(a i ^ 2 + b i ^ 2 + 2 * ρ * a i * b i) / 2) : ℂ))) := by
    apply tendsto_finset_prod
    intro i _
    simpa only [Complex.ofReal_pow, Function.comp_def] using
      Complex.continuous_ofReal.tendsto _ |>.comp (tendsto_correlatedSignCharacteristic_pow ρ (a i) (b i))
  have he : (∏ i, (Real.exp (-(a i ^ 2 + b i ^ 2 + 2 * ρ * a i * b i) / 2) : ℂ)) =
      Complex.exp (-((∑ i, (a i ^ 2 + b i ^ 2 + 2 * ρ * a i * b i) : ℝ) : ℂ) / 2) := by
    simp_rw [Complex.ofReal_exp]
    rw [← Complex.exp_sum]
    congr 1
    push_cast
    rw [← Finset.sum_div, ← Finset.sum_neg_distrib]
  simpa only [sum_noiseKernel_normalizedCubeBlocks_phase,
    integral_exp_correlatedGaussianMeasure hρ, he] using ht

end BooleanAnalysis.GaussianSpace
