/-
Copyright (c) 2026 Lucy Horowitz, Timothe Kasriel, and Mihir Singhal. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lucy Horowitz, Timothe Kasriel, Mihir Singhal
-/

import TCSlib.CommunicationComplexity.DeterministicCC.DetBasic
import TCSlib.CommunicationComplexity.DeterministicCC.FiniteMessage
import TCSlib.CommunicationComplexity.DeterministicCC.DetComplexity
import TCSlib.CommunicationComplexity.DeterministicCC.Rectangle
import TCSlib.CommunicationComplexity.DeterministicCC.DetRectangle
import TCSlib.CommunicationComplexity.DeterministicCC.Rank
import TCSlib.CommunicationComplexity.DeterministicCC.Transcript
import TCSlib.CommunicationComplexity.DeterministicCC.Trees
import TCSlib.CommunicationComplexity.DeterministicCC.Subprotocol
import TCSlib.CommunicationComplexity.DeterministicCC.BalancedSimulation
import TCSlib.CommunicationComplexity.DeterministicCC.DetComposition
import TCSlib.CommunicationComplexity.DeterministicCC.UpperBounds
import TCSlib.CommunicationComplexity.DeterministicCC.OneWay
import TCSlib.CommunicationComplexity.DeterministicCC.Helper
import TCSlib.CommunicationComplexity.DeterministicCC.Hamming
import TCSlib.CommunicationComplexity.DeterministicCC.BitString
import TCSlib.CommunicationComplexity.DeterministicCC.FuncEquality
import TCSlib.CommunicationComplexity.DeterministicCC.FuncDisjointness
import TCSlib.CommunicationComplexity.DeterministicCC.FuncIndexing

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Deterministic Two-Party Communication Complexity

Yao's two-party deterministic model [RY20, Ch. 1], [Yao79]: protocols as binary trees,
their communication complexity, the rectangle structure of protocols and the lower-bound
methods built on it (rectangle counting, fooling sets, log-rank), balanced simulation, one-way
protocols, and the worked examples Equality, Disjointness and Indexing.

## Main results

- `Deterministic.communicationComplexity_le_iff`: characterizes when communication complexity
  is bounded by a given value
- `Deterministic.Protocol.rectangle_partition`: every protocol induces a rectangle partition
  of the input space
- `Deterministic.clog_ncard_le_communicationComplexity`: fooling-set lower bound via log of
  the fooling set size
- `Deterministic.Rank.clog_boolFunctionRank_le_communicationComplexity`: rank lower bound via
  log of the Boolean function matrix rank
- `Deterministic.Protocol.exists_balanced_simulation`: balanced-simulation theorem for
  deterministic protocols
- `Functions.Indexing.oneWayCommunicationComplexity_eq`: exact one-way deterministic
  communication complexity of the Indexing function
- `Functions.Indexing.div_ten_lt_publicCoinOneWay_communicationComplexity_one_ninth`: linear
  lower bound on the one-way public-coin communication complexity of Indexing at error 1/9

## Contents

- `DeterministicCC.DetBasic`: deterministic communication protocols
  (`Deterministic.Protocol`) and runs
- `DeterministicCC.FiniteMessage`: finite-message deterministic protocols
- `DeterministicCC.DetComplexity`: deterministic communication complexity
  (`communicationComplexity_le_iff`)
- `DeterministicCC.Rectangle`: combinatorial rectangles, monochromatic partitions, fooling sets
- `DeterministicCC.DetRectangle`: protocol leaf-rectangle decomposition
  (`rectangle_partition`) and the rectangle / fooling-set lower bounds
- `DeterministicCC.Rank`: log-rank lower bound
  (`clog_boolFunctionRank_le_communicationComplexity`)
- `DeterministicCC.Transcript`: syntactic transcripts of deterministic protocols
- `DeterministicCC.Trees`: protocol tree shape and leaf count
- `DeterministicCC.Subprotocol`: subprotocol embedding and pruning
- `DeterministicCC.BalancedSimulation`: balanced simulation of deterministic protocols
  (`exists_balanced_simulation`)
- `DeterministicCC.DetComposition`: monadic structure and composition of finite-message protocols
- `DeterministicCC.UpperBounds`: trivial upper bounds for deterministic communication complexity
- `DeterministicCC.OneWay`: one-way deterministic protocols and one-way complexity
- `DeterministicCC.Helper`: shared Boolean-input utilities (`BoolInput`, `boolSign`, `flipAt`)
- `DeterministicCC.Hamming`: Hamming balls and spheres (`ballVol`)
- `DeterministicCC.BitString`: signed inner product of bit strings
- `DeterministicCC.FuncEquality`: the Equality function, `D(EQ_n) = n + 1` and its
  public-coin upper bound
- `DeterministicCC.FuncDisjointness`: the set-disjointness function, `D(DISJ_n) = n + 1`
- `DeterministicCC.FuncIndexing`: facade over `FuncIndexing/Basic` (the Indexing function
  and its exact one-way deterministic complexity) and `FuncIndexing/LowerBound` (the linear
  public-coin one-way lower bound)

## References

* [RY20] A. Rao, A. Yehudayoff, *Communication Complexity and Applications*,
  Cambridge University Press, 2020.
* [Rou16] T. Roughgarden, *Communication Complexity (for Algorithm Designers)*,
  Foundations and Trends in Theoretical Computer Science 11(3–4), 2016; arXiv:1509.06257.
* [KN97] E. Kushilevitz, N. Nisan, *Communication Complexity*, Cambridge University
  Press, 1997.
* [Yao79] A. C.-C. Yao, "Some complexity questions related to distributive computing",
  *STOC 1979*, pp. 209–213.

Original formalization by Lucy Horowitz, Timothe Kasriel, Mihir Singhal.
-/

