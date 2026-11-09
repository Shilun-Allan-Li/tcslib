/-
Copyright (c) 2026 Lucy Horowitz, Timothe Kasriel, and Mihir Singhal. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lucy Horowitz, Timothe Kasriel, Mihir Singhal
-/

import TCSlib.CommunicationComplexity.NewmanTheorem.Entropy.Basic
import TCSlib.CommunicationComplexity.NewmanTheorem.Entropy.ChainRules
import TCSlib.CommunicationComplexity.NewmanTheorem.Entropy.Conditioning

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Entropy for Communication Complexity

Bounds, chain rules and invariance lemmas for Shannon entropy `H[X ; μ]`, mutual information
`I[X : Y ; μ]` and conditional mutual information `I[X : Y | Z ; μ]`, built on the PFR
project's definitions (natural-logarithm units throughout). Together they form the
information-theoretic toolkit used by the randomized lower bound for disjointness in
`TCSlib.CommunicationComplexity.NewmanTheorem.FuncDisjointnessLowerBound`.

This module re-exports the whole toolkit; it contains no declarations of its own.

## Contents

- `NewmanTheorem.Entropy.Basic`: entropy bounded by the log of the alphabet size, mutual
  information bounded by entropy, data processing, a.e. congruence and injective recoding
  for mutual information, vanishing for a.e.-constant arguments
- `NewmanTheorem.Entropy.ChainRules`: chain rules for (conditional) mutual information,
  the iterated chain rule over boolean vectors (`boolVectorStrictPrefix`), fiber
  decompositions of the conditioning, monotonicity under coarsening or refining the
  conditioning, nested conditioning of measures
- `NewmanTheorem.Entropy.Conditioning`: a.e. congruence for conditional entropy and
  conditional mutual information, invariance under identical distribution
  (`IdentDistrib.condMutualInfo_eq`) and under injective recoding of the conditioning
  variable, `IdentDistrib.cond_of_pair`

## References

* [RY20] A. Rao, A. Yehudayoff, *Communication Complexity and Applications*,
  Cambridge University Press, 2020.
* [CT06] T. M. Cover, J. A. Thomas, *Elements of Information Theory*, 2nd ed.,
  Wiley, 2006.

Original formalization by Lucy Horowitz, Timothe Kasriel, and Mihir Singhal.
-/
