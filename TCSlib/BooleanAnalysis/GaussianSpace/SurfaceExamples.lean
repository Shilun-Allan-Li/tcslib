/-
Copyright (c) 2026 TCSlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Owen McGinty
-/

import TCSlib.BooleanAnalysis.GaussianSpace.SurfaceRelaxation
import Mathlib.Algebra.MvPolynomial.Degrees
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Examples and upper bounds for Gaussian surface area: statement layer

## Main definitions

Sets are expressed directly in the existing vector carrier, transporting to
`EuclideanSpace` for ball distances. Arbitrary PTF polynomials use `MvPolynomial`.

## Main results

The interval, ball, convex-set, polytope, convex-cone and polynomial-threshold
claims in Example 11.50, with universal constants and placeholder proofs.

## References

* [OD14] Ryan O'Donnell, *Analysis of Boolean Functions*, Cambridge University Press,
  2014; May 2021 arXiv edition, §11.4, Example 11.50, Exercises 11.16–11.17.
* [Bal93] K. Ball, The reverse isoperimetric problem for Gaussian measure,
  Discrete and Computational Geometry 10 (1993), 411–420.
* [Naz03] F. Nazarov, On the maximal perimeter of a convex set in Rn with respect
  to a Gaussian measure, Geometric Aspects of Functional Analysis (2003), 169–187.
* [KOS08] A. Klivans, R. O'Donnell and R. Servedio, Learning geometric concepts
  via Gaussian surface area, FOCS (2008), 541–550.
* [Kan11] D. Kane, The Gaussian surface area and noise sensitivity of degree-d
  polynomial threshold functions, Computational Complexity 20 (2011), 389–412.
-/

open MeasureTheory
open scoped BigOperators ENNReal

namespace BooleanAnalysis.GaussianSpace

open ThresholdFunctions

/-- The surface area of finitely many disjoint nondegenerate closed intervals
is the sum of the Gaussian densities at all endpoints.
[OD14, Example 11.50; Ex. 11.16]

**Proof sketch.** For small rotations each interval endpoint contributes its
one-dimensional crossing limit. The endpoints are separated, so the remaining
crossings vanish after division by the rotation angle. -/
theorem surfaceArea_disjoint_intervals {m : ℕ} (a b : Fin m → ℝ)
    (hab : ∀ j, a j < b j)
    (hdisjoint : Pairwise (fun i j => Disjoint (Set.Icc (a i) (b i)) (Set.Icc (a j) (b j)))) :
    gaussianSurfaceArea {x : Fin 1 → ℝ | ∃ j, a j ≤ x 0 ∧ x 0 ≤ b j} =
      ENNReal.ofReal (∑ j, (standardGaussianPDF (a j) + standardGaussianPDF (b j))) := sorry

/-- An origin-centered Euclidean ball has surface area given by the radial
Gaussian density. [OD14, Example 11.50; Ex. 11.17]

**Proof sketch.** Differentiate the radial Gaussian distribution, whose density
is the chi density, and identify boundary content with rotation perimeter. -/
theorem surfaceArea_centered_ball {n : ℕ} (hn : 0 < n) (r : ℝ) (hr : 0 < r) :
    gaussianSurfaceArea {x : Fin n → ℝ | ‖(WithLp.toLp 2 x : EuclideanSpace ℝ (Fin n))‖ ≤ r} =
      ENNReal.ofReal ((2 : ℝ) ^ (1 - (n : ℝ) / 2) / Real.Gamma ((n : ℝ) / 2) *
        r ^ (n - 1) * Real.exp (-(r ^ 2) / 2)) := sorry

/-- Every translated Euclidean ball has Gaussian surface area at most `√(2/π)`.
[OD14, Example 11.50; KOS08]

**Proof sketch.** Integrate the Gaussian density on the spherical boundary and
use the uniform radial-density estimate, including nonzero centers. -/
theorem surfaceArea_ball_le {n : ℕ} (c : Fin n → ℝ) (r : ℝ) (hr : 0 < r) :
    gaussianSurfaceArea {x : Fin n → ℝ |
      ‖(WithLp.toLp 2 (x - c) : EuclideanSpace ℝ (Fin n))‖ ≤ r} ≤
      ENNReal.ofReal (Real.sqrt (2 / Real.pi)) := sorry

/-- Convex Gaussian sets have surface area `O(n^(1/4))`, uniformly in dimension.
[OD14, Example 11.50; Bal93]

**Proof sketch.** Apply Ball's Gaussian convex-perimeter estimate and identify
the convex boundary content with the existing rotation perimeter. -/
theorem surfaceArea_convex_le :
    ∃ C : ℝ, 0 < C ∧ ∀ {n : ℕ} (A : Set (Fin n → ℝ)),
      MeasurableSet A → Convex ℝ A →
        gaussianSurfaceArea A ≤ ENNReal.ofReal (C * (n : ℝ) ^ (1 / 4 : ℝ)) := sorry

/-- The convex-set dimension exponent one quarter is sharp up to a universal
constant. [OD14, Example 11.50; Naz03]

**Proof sketch.** Use Nazarov's convex polytope construction with many carefully
placed supporting hyperplanes and its Gaussian perimeter lower bound. -/
theorem exists_convex_surfaceArea_ge :
    ∃ c : ℝ, 0 < c ∧ ∀ n : ℕ, 0 < n → ∃ A : Set (Fin n → ℝ),
      IsClosed A ∧ Convex ℝ A ∧
        ENNReal.ofReal (c * (n : ℝ) ^ (1 / 4 : ℝ)) ≤ gaussianSurfaceArea A := sorry

/-- An intersection of `m ≥ 2` halfspaces has surface area `O(√log m)`.
[OD14, Example 11.50; Naz03; KOS08]
The lower bound on `m` prevents the false zero bound at `log 1 = 0`.

**Proof sketch.** Apply Nazarov's polytope perimeter estimate to the given
halfspace representation and transport it to rotation perimeter. -/
theorem surfaceArea_halfspace_intersection_le :
    ∃ C : ℝ, 0 < C ∧ ∀ {n m : ℕ}, 2 ≤ m →
      ∀ (a : Fin m → Fin n → ℝ) (t : Fin m → ℝ),
        gaussianSurfaceArea {x : Fin n → ℝ | ∀ j, ∑ i, a j i * x i ≤ t j} ≤
          ENNReal.ofReal (C * Real.sqrt (Real.log (m : ℝ))) := sorry

/-- The square-root logarithmic halfspace-count bound is sharp up to a universal
constant. [OD14, Example 11.50; Naz03; KOS08]

**Proof sketch.** Choose the threshold of an axis-parallel Gaussian cube so that
the coordinate boundary contributions sum to order the square root of the log
of its dimension. Duplicate a supporting halfspace when needed to match the
specified constraint count. Handle bounded counts by a fixed halfspace. -/
theorem exists_halfspace_intersection_surfaceArea_ge :
    ∃ c : ℝ, 0 < c ∧ ∀ m : ℕ, 2 ≤ m →
      ∃ (n : ℕ) (a : Fin m → Fin n → ℝ) (t : Fin m → ℝ),
        ENNReal.ofReal (c * Real.sqrt (Real.log (m : ℝ))) ≤
          gaussianSurfaceArea {x : Fin n → ℝ | ∀ j, ∑ i, a j i * x i ≤ t j} := sorry

/-- A measurable convex cone with apex at the origin has Gaussian surface area
at most one. [OD14, Example 11.50; KOS08]
The source's word "cone" is interpreted as convex cone: arbitrary unions of
many angular sectors violate this bound. This interpretation was confirmed by
the maintainer when adding the statement layer.

**Proof sketch.** Apply the Gaussian cone perimeter bound to its spherical
cross-section and use conic scaling of the Gaussian radial integral. -/
theorem surfaceArea_convex_cone_le {n : ℕ} (A : Set (Fin n → ℝ))
    (hA : MeasurableSet A) (hconvex : Convex ℝ A)
    (hcone : ∀ x ∈ A, ∀ t : ℝ, 0 ≤ t → t • x ∈ A) :
    gaussianSurfaceArea A ≤ 1 := sorry

/-- A degree-`k` polynomial threshold set has Gaussian surface area at most
`k/√(2π)`. The polynomial need not be multilinear.
[OD14, Example 11.50; Kan11]

**Proof sketch.** Restrict the polynomial to Gaussian rotation circles. The
number of sign transitions is at most twice its degree; average this count
and take the infinitesimal rotation limit. -/
theorem surfaceArea_polynomial_threshold_le {n k : ℕ}
    (p : MvPolynomial (Fin n) ℝ) (hp : p.totalDegree ≤ k) :
    gaussianSurfaceArea {x : Fin n → ℝ | 0 ≤ MvPolynomial.eval x p} ≤
      ENNReal.ofReal ((k : ℝ) / Real.sqrt (2 * Real.pi)) := sorry

/-- The degree bound for polynomial thresholds is approached arbitrarily
closely already in dimension one. [OD14, Example 11.50; Kan11]
Sharpness means an arbitrarily close lower bound, not exact attainment by a
polynomial with repeated roots.

**Proof sketch.** Place `k` distinct real roots arbitrarily close to zero.
The interval endpoint formula makes the perimeter the sum of their densities,
which approaches `k` times the maximum Gaussian density. -/
theorem exists_polynomial_threshold_surfaceArea_ge (k : ℕ) (ε : ℝ) (hε : 0 < ε) :
    ∃ p : MvPolynomial (Fin 1) ℝ, p.totalDegree ≤ k ∧
      ENNReal.ofReal ((k : ℝ) / Real.sqrt (2 * Real.pi) - ε) ≤
        gaussianSurfaceArea {x : Fin 1 → ℝ | 0 ≤ MvPolynomial.eval x p} := sorry

end BooleanAnalysis.GaussianSpace
