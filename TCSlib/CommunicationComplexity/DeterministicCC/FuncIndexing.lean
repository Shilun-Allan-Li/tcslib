/-
Copyright (c) 2026 Lucy Horowitz, Timothe Kasriel, and Mihir Singhal. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lucy Horowitz, Timothe Kasriel, Mihir Singhal
-/

import TCSlib.CommunicationComplexity.DeterministicCC.FuncIndexing.Basic
import TCSlib.CommunicationComplexity.DeterministicCC.FuncIndexing.LowerBound

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Indexing

The Index problem: Alice holds an `n`-bit string `x`, Bob holds an index `i`, and Bob must
output the bit `x i` [Rou16, §2.4 Definition (Index)]. This module collects the exact
deterministic one-way complexity `n` (a pigeonhole argument on Alice's messages) and the
linear public-coin one-way lower bound of Kremer–Nisan–Ron via Yao's distributional method,
with explicit constants: for `n ≥ 300`, every protocol with error `1/9` needs more than
`n/10` bits.

## Contents

- `DeterministicCC.FuncIndexing.Basic`: the Index function `Functions.Indexing.indexing`,
  the trivial protocols, the exact one-way deterministic complexity
  `Functions.Indexing.oneWayCommunicationComplexity_eq`, the two-way upper bound
  `Functions.Indexing.communicationComplexity_le`, and the uniform input distribution
  `Functions.Indexing.indexingInputDist`
- `DeterministicCC.FuncIndexing.LowerBound`: the bad-input combinatorics, the explicit
  counting lemmas, `Functions.Indexing.one_ninth_lt_distributionalError_of_cost_le` and the
  public-coin one-way lower bound
  `Functions.Indexing.div_ten_lt_publicCoinOneWay_communicationComplexity_one_ninth`

## References

* [Rou16] T. Roughgarden, *Communication Complexity (for Algorithm Designers)*,
  Foundations and Trends in Theoretical Computer Science 11(3–4), 2016; arXiv:1509.06257.
* [KNR99] I. Kremer, N. Nisan, D. Ron, "On randomized one-round communication complexity",
  *Computational Complexity* 8(1):21–49, 1999.
* [KN97] E. Kushilevitz, N. Nisan, *Communication Complexity*, Cambridge University Press,
  1997.

Original formalization by Lucy Horowitz, Timothe Kasriel, and Mihir Singhal.
-/
