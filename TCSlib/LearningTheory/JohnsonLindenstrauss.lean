/-
Copyright (c) 2026 Ganesh Sankar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ganesh Sankar
-/
import TCSlib.LearningTheory.JohnsonLindenstrauss.Bernstein
import TCSlib.LearningTheory.JohnsonLindenstrauss.RowDistribution
import TCSlib.LearningTheory.JohnsonLindenstrauss.ChiSquaredMGF
import TCSlib.LearningTheory.JohnsonLindenstrauss.ConcentrationBound
import TCSlib.LearningTheory.JohnsonLindenstrauss.SubGaussian
import TCSlib.LearningTheory.JohnsonLindenstrauss.Rademacher
import TCSlib.LearningTheory.JohnsonLindenstrauss.UnionBound
import TCSlib.LearningTheory.JohnsonLindenstrauss.Main

/-!
# Johnson–Lindenstrauss Lemma

Random linear maps into `k = O(log n / ε²)` dimensions preserve all pairwise distances of
`n` points up to `(1 ± ε)`. Both the Gaussian path and the sub-Gaussian/Rademacher path
are fully proved; the latter rests on `subgaussian_centered_sq_bernstein` (Vershynin
Lemma 2.7.6), proved by Gaussian decoupling and a fourth-moment bound.

## Contents

- `JohnsonLindenstrauss.Bernstein`: `HasBernsteinMGF` predicate, closure under independent sums,
  Chernoff tails
- `JohnsonLindenstrauss.RowDistribution`: bad event `BadSingle`; rows of `Ax` are iid Gaussian
- `JohnsonLindenstrauss.ChiSquaredMGF`: Gaussian quadratic MGF, Taylor bound, chi-squared tail
- `JohnsonLindenstrauss.ConcentrationBound`: single-vector concentration (Gaussian and
  Bernstein-abstract)
- `JohnsonLindenstrauss.SubGaussian`: the Hanson–Wright-type bound; sub-Gaussian single-vector bound
- `JohnsonLindenstrauss.Rademacher`: the `±1/√k` matrix, sub-Gaussian rows, exact variance
- `JohnsonLindenstrauss.UnionBound`: `IsJLEmbedding`, union bound, probabilistic-method extraction
- `JohnsonLindenstrauss.Main`: iid Gaussian sample space; headline theorems and corollaries
-/
