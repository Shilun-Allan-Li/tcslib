import TCSlib.BooleanAnalysis.Basic
import Mathlib.Algebra.Notation.Indicator
import Mathlib.Analysis.SpecialFunctions.Pow.Real

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Shared probability and norm definitions on the uniform cube

## Main definitions

* `cubeIndicator`, `cubeProbability`: the standard indicator and its uniform expectation.
* `cubeVariance`: the second centered moment.
* `cubeLpNorm`: the real-exponent power-mean expression shared by forward and reverse
  hypercontractivity. The reverse mean retains its separate conventions at nonpositive
  exponents.

## Main results

This lightweight file contains definitions shared by the cube applications.

## References

* [OD14] Ryan O'Donnell, *Analysis of Boolean Functions*, Cambridge University Press, 2014;
  May 2021 arXiv edition, §§9.1–9.2 and §9.5, Theorems 9.7 and 9.21–9.22.
-/

open scoped Classical

namespace BooleanAnalysis.Hypercontractivity

/-- The indicator of a cube event is one on the event and zero elsewhere.
[OD14, §9.1] This reuses Mathlib's set indicator. -/
noncomputable def cubeIndicator {n : ℕ} (A : BoolCube n → Prop) : BooleanFunc n :=
  Set.indicator {x | A x} (fun _ => 1)

/-- Uniform event probability is the expectation of its indicator. [OD14, §9.1] -/
noncomputable def cubeProbability {n : ℕ} (A : BoolCube n → Prop) : ℝ :=
  expect (cubeIndicator A)

/-- Variance on the uniform cube is the second centered moment. [OD14, Thm. 9.7] -/
noncomputable def cubeVariance {n : ℕ} (f : BooleanFunc n) : ℝ :=
  expect (fun x => (f x - expect f) ^ 2)

/-- The real-exponent `Lᵖ` expression on the uniform cube; applications use `p ≥ 1`.
[OD14, §9.5, Thms. 9.21–9.22] The raw formula is retained at every real exponent so the
reverse-hypercontractivity mean can reuse it without changing its boundary conventions. -/
noncomputable abbrev cubeLpNorm {n : ℕ} (p : ℝ) (f : BooleanFunc n) : ℝ :=
  (expect (fun x => |f x| ^ p)) ^ (1 / p)

end BooleanAnalysis.Hypercontractivity
