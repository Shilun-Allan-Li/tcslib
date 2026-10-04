/-
Copyright (c) 2026 Lucy Horowitz, Timothe Kasriel, and Mihir Singhal. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lucy Horowitz, Timothe Kasriel, Mihir Singhal
-/

import TCSlib.CommunicationComplexity.NewmanTheorem.FiniteProbabilitySpace
import TCSlib.CommunicationComplexity.NewmanTheorem.CoinTape
import TCSlib.CommunicationComplexity.NewmanTheorem.PublicCoinBasic
import TCSlib.CommunicationComplexity.NewmanTheorem.PublicCoinFiniteMessage
import TCSlib.CommunicationComplexity.NewmanTheorem.PublicCoinComplexity
import TCSlib.CommunicationComplexity.NewmanTheorem.PrivateCoinBasic
import TCSlib.CommunicationComplexity.NewmanTheorem.PrivateCoinFiniteMessage
import TCSlib.CommunicationComplexity.NewmanTheorem.PrivateCoinComplexity
import TCSlib.CommunicationComplexity.NewmanTheorem.PrivateCoinApproximation
import TCSlib.CommunicationComplexity.NewmanTheorem.PublicCoinApproximation
import TCSlib.CommunicationComplexity.NewmanTheorem.Derandomization
import TCSlib.CommunicationComplexity.NewmanTheorem.Comparison
import TCSlib.CommunicationComplexity.NewmanTheorem.Newman
import TCSlib.CommunicationComplexity.NewmanTheorem.Minimax
import TCSlib.CommunicationComplexity.NewmanTheorem.PublicCoinOneWay
import TCSlib.CommunicationComplexity.NewmanTheorem.OneWayMinimax
import TCSlib.CommunicationComplexity.NewmanTheorem.Discrepancy
import TCSlib.CommunicationComplexity.NewmanTheorem.PublicCoinComposition
import TCSlib.CommunicationComplexity.NewmanTheorem.PrivateCoinComposition
import TCSlib.CommunicationComplexity.NewmanTheorem.FuncInnerProduct
import TCSlib.CommunicationComplexity.NewmanTheorem.FuncHash
import TCSlib.CommunicationComplexity.NewmanTheorem.Entropy
import TCSlib.CommunicationComplexity.NewmanTheorem.KLDivergence
import TCSlib.CommunicationComplexity.NewmanTheorem.TVDistance
import TCSlib.CommunicationComplexity.NewmanTheorem.Pinsker
import TCSlib.CommunicationComplexity.NewmanTheorem.FuncDisjointnessLowerBound

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Newman's Theorem: Public Coin to Private Coin Reduction

## Main results

- `PublicCoin.newman`: every public-coin protocol can be simulated by a private-coin
  protocol with only `⌈log₂ t⌉ = O(log log(|X|·|Y|) + log(1/ε))` additional bits of
  communication, `t = O(log(|X|·|Y|)/ε²)`
- `PublicCoin.FiniteMessage.Protocol.newmanProtocol_ApproxComputes`: the Newman
  private-coin protocol approximately computes the same function as the original
  public-coin protocol
- `PublicCoin.FiniteMessage.Protocol.newmanProtocol_complexity`: the complexity of the
  Newman protocol equals the log of the number of derandomization samples plus the
  original protocol's complexity

## Contents

- `NewmanTheorem.FiniteProbabilitySpace`: finite probability spaces
  (`FiniteProbabilitySpace`), uniform measures, product measures
- `NewmanTheorem.CoinTape`: uniform probability measure on finite coin sequences
- `NewmanTheorem.PublicCoinBasic`: public-coin protocols (`PublicCoin.Protocol`) and runs
- `NewmanTheorem.PublicCoinFiniteMessage`: public-coin protocols with finite message sets
- `NewmanTheorem.PublicCoinComplexity`: public-coin communication complexity
- `NewmanTheorem.PrivateCoinBasic`: private-coin protocols (`PrivateCoin.Protocol`) and runs
- `NewmanTheorem.PrivateCoinFiniteMessage`: private-coin protocols with finite message sets
- `NewmanTheorem.PrivateCoinComplexity`: private-coin communication complexity
- `NewmanTheorem.PrivateCoinApproximation`: approximate computation by private-coin protocols
- `NewmanTheorem.PublicCoinApproximation`: approximate computation by public-coin protocols
- `NewmanTheorem.Derandomization`: Chernoff + union bound (`exists_good_randomness`,
  `derandomizationSamples`)
- `NewmanTheorem.Comparison`: conversions between deterministic, private-coin, and
  public-coin protocols
- `NewmanTheorem.Newman`: Newman's theorem (`newmanIndexSpace`, `newmanProtocol`, `newman`)
- `NewmanTheorem.Minimax`: distributional complexity and Yao's minimax principle
- `NewmanTheorem.PublicCoinOneWay`: one-way public-coin protocols
- `NewmanTheorem.OneWayMinimax`: minimax for one-way protocols
- `NewmanTheorem.Discrepancy`: the discrepancy method
- `NewmanTheorem.PublicCoinComposition`: composition of public-coin protocols
- `NewmanTheorem.PrivateCoinComposition`: composition of private-coin protocols
- `NewmanTheorem.FuncInnerProduct`: the inner product function and its discrepancy bound
- `NewmanTheorem.FuncHash`: hash function collision probability
- `NewmanTheorem.Entropy`: Shannon entropy on finite probability spaces (facade over
  `NewmanTheorem.Entropy.Basic` (entropy, conditional entropy, mutual information
  basics), `NewmanTheorem.Entropy.ChainRules` (chain rules, subadditivity,
  `boolVectorStrictPrefix`) and `NewmanTheorem.Entropy.Conditioning` (a.e. congruence
  and `IdentDistrib` transfer lemmas for conditional mutual information))
- `NewmanTheorem.KLDivergence`: Kullback-Leibler divergence
- `NewmanTheorem.TVDistance`: total variation distance
- `NewmanTheorem.Pinsker`: Pinsker's inequality
- `NewmanTheorem.FuncDisjointnessLowerBound`: the randomized lower bound for set
  disjointness (sub-facade)

## References

* [RY20] A. Rao, A. Yehudayoff, *Communication Complexity and Applications*,
  Cambridge University Press, 2020.
* [Rou16] T. Roughgarden, *Communication Complexity (for Algorithm Designers)*,
  Foundations and Trends in Theoretical Computer Science 11(3–4), 2016;
  arXiv:1509.06257.
* [New91] I. Newman, "Private vs. common random bits in communication complexity",
  *Information Processing Letters* 39(2):67–71, 1991.
* [KN97] E. Kushilevitz, N. Nisan, *Communication Complexity*, Cambridge University
  Press, 1997.

Original formalization by Lucy Horowitz, Timothe Kasriel, Mihir Singhal.
-/
