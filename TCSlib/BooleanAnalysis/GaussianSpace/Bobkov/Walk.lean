/-
Copyright (c) 2026 TCSlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Owen McGinty
-/

import TCSlib.BooleanAnalysis.GaussianSpace.Bobkov
import Mathlib.Probability.Martingale.Basic
import Mathlib.Topology.ContinuousMap.Bounded.Basic

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# The stopped-walk claim in the source's Bobkov proof: statement layer

## Main definitions

* `IsAbsorbedFairWalk`: the source walk specified by its initial value,
  adapted lattice path and conditional transition law. Filtrations, conditional
  expectation and submartingales use Mathlib's definitions.

## Main results

Claim 11.54 as a stochastic-process statement, with an intentionally unfilled
proof. The already proved Boolean Bobkov results use a different argument and
do not depend on this optional source-proof branch. No recursive walk host,
stopping-time implementation or new probability model is introduced.

## References

* [OD14] Ryan O'Donnell, *Analysis of Boolean Functions*, Cambridge University Press,
  2014; May 2021 arXiv edition, §11.4, Claim 11.54 and equation (11.20).
-/

open MeasureTheory Filter
open scoped ProbabilityTheory

namespace BooleanAnalysis.GaussianSpace

/-- An absorbed fair walk starts at `a`, stays on the step-τ lattice in
`[a-b,a+b]`, and conditionally makes fair ±τ steps until an endpoint, where
it stays. The transition identity for bounded continuous tests specifies the
conditional probability law. [OD14, §11.4, walk preceding Claim 11.54] -/
structure IsAbsorbedFairWalk {Ω : Type*} [mΩ : MeasurableSpace Ω]
    (Y : ℕ → Ω → ℝ) (ℱ : Filtration ℕ mΩ) (μ : Measure Ω) (a b τ : ℝ) : Prop where
  /-- The source walk starts at its midpoint. -/
  initial : Y 0 =ᵐ[μ] fun _ => a
  /-- Each value is known at its time in the filtration. -/
  adapted : Adapted ℱ Y
  /-- The values stay on the lattice between the absorbing barriers. -/
  lattice : ∀ t, ∀ᵐ ω ∂μ,
    Y t ω ∈ Set.Icc (a - b) (a + b) ∧ ∃ z : ℤ, Y t ω = a + τ * z
  /-- The full past determines the symmetric next-step law through the current value. -/
  transition : ∀ (t : ℕ) (φ : BoundedContinuousFunction ℝ ℝ),
    μ[fun ω => φ (Y (t + 1) ω) | ℱ t] =ᵐ[μ]
      fun ω => if Y t ω = a - b ∨ Y t ω = a + b then φ (Y t ω)
        else (φ (Y t ω + τ) + φ (Y t ω - τ)) / 2

/-- For a sufficiently small step, the Gaussian profile length with accumulated
time coordinate is a submartingale along an absorbed fair walk.
[OD14, Claim 11.54]
The condition `b=mτ` ensures that both absorbing endpoints lie on its lattice.
The filtration records the whole history, matching the source's conditional statement.

**Proof sketch.** At a stopped endpoint the time coordinate can only increase.
At an interior point apply the two-point Bobkov inequality with an additional
fixed Euclidean time coordinate, then use the fair conditional transition law.
The path is bounded, so all profile-length variables are integrable. Iterate
the one-step conditional inequality through the filtration. -/
theorem bobkov_walk_submartingale :
    ∀ δ : ℝ, 0 < δ → ∃ τ0 : ℝ, 0 < τ0 ∧
      ∀ {Ω : Type*} [mΩ : MeasurableSpace Ω]
      (μ : Measure Ω) [IsProbabilityMeasure μ] (ℱ : Filtration ℕ mΩ)
      (Y : ℕ → Ω → ℝ) (a b τ : ℝ),
      0 < b → 0 < τ → τ ≤ τ0 →
      δ ≤ a - b → a + b ≤ 1 - δ → (∃ m : ℕ, b = m * τ) →
      IsAbsorbedFairWalk Y ℱ μ a b τ →
        Submartingale
          (fun t ω => Real.sqrt (closedGaussianProfile (Y t ω) ^ 2 + τ ^ 2 * t)) ℱ μ := sorry

end BooleanAnalysis.GaussianSpace
