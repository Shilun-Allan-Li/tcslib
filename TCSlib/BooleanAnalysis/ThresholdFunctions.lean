import TCSlib.BooleanAnalysis.ThresholdFunctions.Basic
import TCSlib.BooleanAnalysis.ThresholdFunctions.BitFlipSets
import TCSlib.BooleanAnalysis.ThresholdFunctions.DegreeOne
import TCSlib.BooleanAnalysis.ThresholdFunctions.Fourier
import TCSlib.BooleanAnalysis.ThresholdFunctions.Gaussian
import TCSlib.BooleanAnalysis.ThresholdFunctions.GaussianPolar
import TCSlib.BooleanAnalysis.ThresholdFunctions.GaussianTail
import TCSlib.BooleanAnalysis.ThresholdFunctions.LinearThresholdInfluence
import TCSlib.BooleanAnalysis.ThresholdFunctions.Majority
import TCSlib.BooleanAnalysis.ThresholdFunctions.NoiseStability

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Majority and threshold functions

This facade re-exports the formalization skeleton for Chapter 5 of O'Donnell's *Analysis of Boolean
Functions*.

## Main definitions

Linear and polynomial threshold representations, Gaussian notation, Fourier-weight notation, and
uniform noise stability.

## Main results

Chow-type uniqueness, low-degree Fourier bounds, majority's exact and asymptotic spectrum,
degree-one inequalities, Peres's theorem, and Kane's polynomial-threshold influence bound.

## Contents

* `ThresholdFunctions.Basic`: representations, sparsity, Fourier weights, distance, and stability.
* `ThresholdFunctions.Fourier`: Chow theorems, low-degree weight, and sparse PTF results.
* `ThresholdFunctions.Gaussian`: central-limit and regular-threshold statements.
* `ThresholdFunctions.GaussianTail`: Mills-ratio bounds and the asymptotics of the Gaussian
  isoperimetric profile near zero.
* `ThresholdFunctions.Majority`: exact and asymptotic Fourier coefficients of majority.
* `ThresholdFunctions.DegreeOne`: Level-1, pi-over-two, and FKN consequence statements.
* `ThresholdFunctions.LinearThresholdInfluence`: unateness and the `sqrt n` total-influence bound
  for linear threshold functions.
* `ThresholdFunctions.NoiseStability`: Peres's theorem and polynomial-threshold stability.

## References

* [OD14] Ryan O'Donnell, *Analysis of Boolean Functions*, Cambridge University Press, 2014;
  arXiv edition, 2021, Chapter 5.
-/
