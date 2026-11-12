/-
Copyright (c) 2026 Lucy Horowitz, Timothe Kasriel, and Mihir Singhal. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lucy Horowitz, Timothe Kasriel, Mihir Singhal
-/

import TCSlib.CommunicationComplexity.NewmanTheorem.FuncDisjointnessLowerBound.HardSample
import TCSlib.CommunicationComplexity.NewmanTheorem.FuncDisjointnessLowerBound.ZVariable
import TCSlib.CommunicationComplexity.NewmanTheorem.FuncDisjointnessLowerBound.DisjointModel
import TCSlib.CommunicationComplexity.NewmanTheorem.FuncDisjointnessLowerBound.DualHardSample
import TCSlib.CommunicationComplexity.NewmanTheorem.FuncDisjointnessLowerBound.HardDistributionEvents
import TCSlib.CommunicationComplexity.NewmanTheorem.FuncDisjointnessLowerBound.CoordinateVectorModel
import TCSlib.CommunicationComplexity.NewmanTheorem.FuncDisjointnessLowerBound.DualityMeasurePreserving
import TCSlib.CommunicationComplexity.NewmanTheorem.FuncDisjointnessLowerBound.ZFiberMeasure
import TCSlib.CommunicationComplexity.NewmanTheorem.FuncDisjointnessLowerBound.RectangleSwitching
import TCSlib.CommunicationComplexity.NewmanTheorem.FuncDisjointnessLowerBound.InformationTerms
import TCSlib.CommunicationComplexity.NewmanTheorem.FuncDisjointnessLowerBound.AliceYFalse
import TCSlib.CommunicationComplexity.NewmanTheorem.FuncDisjointnessLowerBound.Headline

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Randomized Communication Complexity Lower Bound for Disjointness

The linear lower bound `R^pub_{1/32}(DISJ_n) > ⌊n / 2^32⌋` on the public-coin randomized
communication complexity of set disjointness [RY20, Thm 6.13], originally due to
Kalyanasundaram–Schnitger [KS92] and Razborov [Raz92], proved by the information-complexity
method of Bar-Yossef–Jayram–Kumar–Sivakumar [BJKS04] as presented in [RY20, Ch. 6]. This
facade only re-exports the twelve pieces listed under `## Contents`; the declarations live
in the namespace `Functions.Disjointness.RandomizedLowerBound`.

**Roadmap.** By Yao's minimax principle it suffices to show that under Razborov's hard
distribution — a uniform special coordinate `T`, independent uniform bits at `T`, and a
uniform pair from `{00, 01, 10}` at every other coordinate — every deterministic protocol of
communication `ℓ < c · n` errs with probability more than `1/32`. Pieces 1–5 build the
sample space, the transcript variable `Z = (S, T, A_<T, B_>T)`, and the conditioned laws;
pieces 6–9 prove that, conditioned on disjointness, the coordinates are independent with
`T` independent of the inputs, that the Alice/Bob duality preserves everything, and that on
each `Z`-fiber the special pair `(A_T, B_T)` has a product law [RY20, Claim 6.14]. Piece 10
bounds the information `claimInfo` about the special bits revealed by the transcript from
above by `2 ℓ · log 2 / n`, via the chain rule [RY20, Lemma 6.15] and averaging over `T`
[RY20, eq. (6.3)]. Pieces 11–12 bound it from below by a constant for any protocol of error
at most `1/32` [RY20, eq. (6.2)]: if the information is small then, by Pinsker and Markov,
most `Z`-fibers see a nearly uniform special pair, and on such a fiber the protocol's fixed
answer is wrong with conditional probability about `1/4`. Comparing the two bounds gives
`ℓ = Ω(n)`; the module docstring of `Headline.lean` spells the chain out in detail.

## Main definitions

All declarations are in the namespace `Functions.Disjointness.RandomizedLowerBound`.

* `HardSample`: the hard sample space carrying Razborov's distribution (`HardSample.lean`).
* `inputDist`: the induced hard distribution on input pairs (`ZVariable.lean`).
* `zVariable`: the transcript variable `Z = (S, T, A_<T, B_>T)` (`ZVariable.lean`).
* `disjointCondMeasure`: the hard distribution conditioned on disjointness
  (`HardDistributionEvents.lean`).
* `aliceInfoTerm`: Alice's corrected special-coordinate information term
  `I(A_T : S | T A_<T B_≥T 𝒟)` (`InformationTerms.lean`).
* `claimInfo`: the sum of Alice's and Bob's terms, the quantity bounded from both sides
  (`InformationTerms.lean`).
* `goodZ`: the `Z` values on whose fiber the special pair is within `2γ` of uniform
  (`RectangleSwitching.lean`).

## Main results

All in `Headline.lean`.

* `floor_div_pow_lt_publicCoin_communicationComplexity_disjointness`: the public-coin
  randomized communication complexity of disjointness on `n` elements at error `1/32` is
  strictly greater than `⌊n / 2^32⌋` — a linear lower bound at fixed error [RY20, Thm 6.13].
* `lt_publicCoin_communicationComplexity_disjointness_of_lt_const_mul_n`: every `k` below
  `(1/32768)² n / (3 log 2)` is less than that communication complexity.
* `const_mul_n_le_complexity_of_distributionalError_le`: a deterministic protocol with
  distributional error `≤ 1/32` under the hard distribution has communication at least
  `(1/32768)² n / (3 log 2)`.
* `one_div_32768_sq_lt_claimInfo_of_distributionalError_le`: a deterministic protocol with
  distributional error `≤ 1/32` has `claimInfo > (1/32768)²`.

## Contents

* `FuncDisjointnessLowerBound.HardSample`: the hard sample space (`HardSample`,
  `DisjointCoordinate`, uniform laws, accessors, events, conditioning recodings).
* `FuncDisjointnessLowerBound.ZVariable`: protocol/transcript types, the transcript variable
  `Z` (`rawZVariable`, `zVariable`, `zFiber`), `inputDist`, `dualProtocol`.
* `FuncDisjointnessLowerBound.DisjointModel`: the disjoint model, `coordinateOfBits`, `mix`,
  `disjointEvent` cardinalities.
* `FuncDisjointnessLowerBound.DualHardSample`: the Alice/Bob involution `dualHardSample` and
  its interaction with `mix`.
* `FuncDisjointnessLowerBound.HardDistributionEvents`: event masses under the hard
  distribution, `disjointCondMeasure`, `disjointSpecialYFalseMeasure`, independence of
  coordinates.
* `FuncDisjointnessLowerBound.CoordinateVectorModel`: the coordinate vector model,
  conditional independence, `identDistrib_*` transfers.
* `FuncDisjointnessLowerBound.DualityMeasurePreserving`: `dualHardSample` is measure
  preserving, `message`, `dualZValue`, `protocolErrorEvent`.
* `FuncDisjointnessLowerBound.ZFiberMeasure`: `zFiberMeasure`, conditional special-pair laws,
  `xDistance`/`yDistance`, Pinsker/Jensen/Markov steps.
* `FuncDisjointnessLowerBound.RectangleSwitching`: `goodZ`, rectangle switching
  (`conditionalSpecialPairLaw_eq_prod`, [RY20, Claim 6.14]).
* `FuncDisjointnessLowerBound.InformationTerms`: `aliceInfoTerm`, `bobInfoTerm`, `claimInfo`,
  the chain rule [RY20, Lemma 6.15] and the averaging bounds [RY20, eq. (6.3)].
* `FuncDisjointnessLowerBound.AliceYFalse`: the `Y_T = 0` branch
  (`aliceInfoTermSpecialYFalse`, `flipSpecialX`, the average-divergence identity).
* `FuncDisjointnessLowerBound.Headline`: the headline theorems
  (`floor_div_pow_lt_publicCoin_communicationComplexity_disjointness` and friends).

## References

* [RY20] A. Rao, A. Yehudayoff, *Communication Complexity and Applications*,
  Cambridge University Press, 2020.
* [Raz92] A. A. Razborov, "On the distributional complexity of disjointness",
  *Theoretical Computer Science* 106(2):385–390, 1992.
* [KS92] B. Kalyanasundaram, G. Schnitger, "The probabilistic communication complexity of
  set intersection", *SIAM J. Discrete Math.* 5(4):545–557, 1992.
* [BJKS04] Z. Bar-Yossef, T. S. Jayram, R. Kumar, D. Sivakumar, "An information statistics
  approach to data stream and communication complexity", *J. Comput. Syst. Sci.*
  68(4):702–732, 2004.

Original formalization by Lucy Horowitz, Timothe Kasriel, and Mihir Singhal.
-/
