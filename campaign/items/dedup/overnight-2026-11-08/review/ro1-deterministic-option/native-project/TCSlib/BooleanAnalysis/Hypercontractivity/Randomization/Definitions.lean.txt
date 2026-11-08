/-
Copyright (c) 2026 TCSlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Owen McGinty
-/

import TCSlib.BooleanAnalysis.Hypercontractivity.Products.Basic
import TCSlib.BooleanAnalysis.Hypercontractivity.Cube.Definitions

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Randomization and notable-coordinate definitions

## Main definitions

* `randomization`, `randomizationNorm`: independent signs on orthogonal components.
* `coordinateNoise`, `anisotropicNoise`: noise with arbitrary real coordinate rates.
* `localSpectralInfluence`, `notableCoordinates`, `notableFamily`: the objects in
  the proof of Bourgain's structural theorem.

## Main results

Definitions only; all objects have explicit finite-sum bodies.

## References

* [OD14] Ryan O'Donnell, *Analysis of Boolean Functions*, Cambridge University Press, 2014;
  May 2021 arXiv edition, Definitions 10.32 and 10.40, Theorem 10.47 and its proof.
-/

open scoped BigOperators Classical

namespace BooleanAnalysis.Hypercontractivity

variable {n : ℕ}

universe u

/-- Randomization attaches an independent Walsh sign to each orthogonal component.
[OD14, Def. 10.32] The same coordinatewise construction permits different coordinate spaces. -/
noncomputable def randomization {n : ℕ} (P : FiniteProduct.{u} n)
    (f : P.Point → ℝ) (r : BoolCube n) (x : P.Point) : ℝ :=
  ∑ S : Finset (Fin n), chiS S r * P.component S f x

/-- The randomization norm averages over both independent signs and product inputs.
[OD14, Def. 10.32 and Thm. 10.35] -/
noncomputable def randomizationNorm {n : ℕ} (P : FiniteProduct.{u} n)
    (q : ℝ) (f : P.Point → ℝ) : ℝ :=
  (P.expect (fun x => expect (fun r => |randomization P f r x| ^ q))) ^ (1 / q)

/-- Noise in coordinate `i` preserves its conditional mean and scales its centered part.
[OD14, Def. 10.40] -/
noncomputable def coordinateNoise {n : ℕ} (P : FiniteProduct.{u} n)
    (i : Fin n) (ρ : ℝ) (f : P.Point → ℝ) (x : P.Point) : ℝ :=
  f x - P.laplacian i f x + ρ * P.laplacian i f x

/-- Anisotropic noise multiplies component `S` by the product of its coordinate rates.
The spectral formula allows arbitrary real rates. [OD14, Def. 10.40, equation (10.15)] -/
noncomputable def anisotropicNoise {n : ℕ} (P : FiniteProduct.{u} n)
    (r : Fin n → ℝ) (f : P.Point → ℝ) (x : P.Point) : ℝ :=
  ∑ S : Finset (Fin n), (∏ i ∈ S, r i) * P.component S f x

/-- Pointwise spectral influence sums squared components containing the given coordinate.
[OD14, proof of Thm. 10.47] -/
noncomputable def localSpectralInfluence {n : ℕ} (P : FiniteProduct.{u} n)
    (f : P.Point → ℝ) (i : Fin n) (x : P.Point) : ℝ :=
  ∑ S : Finset (Fin n), if i ∈ S then P.component S f x ^ 2 else 0

/-- The initial notable coordinates at an input have pointwise spectral influence at least
the specified threshold. [OD14, proof of Thm. 10.47, the set `J′ₓ`] -/
noncomputable def notableCoordinates {n : ℕ} (P : FiniteProduct.{u} n)
    (f : P.Point → ℝ) (τ : ℝ) (x : P.Point) : Finset (Fin n) :=
  Finset.univ.filter (fun i => τ ≤ localSpectralInfluence P f i x)

/-- The retained family consists of subsets of `J` of size at most the real cutoff `k`.
[OD14, Thm. 10.47, the family `Fₓ`] -/
noncomputable def notableFamily {n : ℕ} (J : Finset (Fin n)) (k : ℝ) :
    Finset (Finset (Fin n)) :=
  J.powerset.filter (fun S => (S.card : ℝ) ≤ k)

end BooleanAnalysis.Hypercontractivity
