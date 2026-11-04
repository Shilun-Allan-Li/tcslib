/-
Copyright (c) 2026 The TCSlib Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TCSlib Contributors
-/
import TCSlib.Complexity.Randomized.SchwartzZippel
import TCSlib.Complexity.Randomized.ErrorReduction
import TCSlib.Complexity.Randomized.Classes
import TCSlib.Complexity.Randomized.Adleman
import TCSlib.Complexity.Randomized.SipserGacs
import TCSlib.Complexity.Randomized.PolyTimeModel
import TCSlib.Complexity.Randomized.PTM
import TCSlib.Complexity.Randomized.Inclusions
import TCSlib.Complexity.Randomized.PTMEquiv
import TCSlib.Complexity.Randomized.Median
import TCSlib.Complexity.Randomized.PrimalityMath
import TCSlib.Complexity.Randomized.Primality
import TCSlib.Complexity.Randomized.AlgCircuit
import TCSlib.Complexity.Randomized.RandomBits
import TCSlib.Complexity.Randomized.Fingerprint
import TCSlib.Complexity.Randomized.ZeroPEval
import TCSlib.Complexity.Randomized.ZeroPRun
import TCSlib.Complexity.Randomized.ZeroP
import TCSlib.Complexity.Randomized.ZeroPPIT
import TCSlib.Complexity.Randomized.MatchingMath
import TCSlib.Complexity.Randomized.Matching
import TCSlib.Complexity.Randomized.ExpectedTime
import TCSlib.Complexity.Randomized.Coins
import TCSlib.Complexity.Randomized.ZPPEquiv
import TCSlib.Complexity.Randomized.ZPPHosts
import TCSlib.Complexity.Randomized.ZPPHostsClasses
import TCSlib.Complexity.Randomized.Reductions
import TCSlib.Complexity.Randomized.NPPoly
import TCSlib.Complexity.Randomized.Yap
import TCSlib.Complexity.Randomized.DirectedWalk
import TCSlib.Complexity.Randomized.BPPHard
import TCSlib.Complexity.Randomized.BPLInPCount
import TCSlib.Complexity.Randomized.BPLInPWords
import TCSlib.Complexity.Randomized.BPLInP
import TCSlib.Complexity.Randomized.RandomWalkCover
import TCSlib.Complexity.Randomized.RandomWalkMixing
import TCSlib.Complexity.Randomized.RandomWalkMixingPad
import TCSlib.Complexity.Randomized.UniformSample
import TCSlib.Complexity.Randomized.BiasedCoin
import TCSlib.Complexity.Randomized.BiasedCoinHalting
import TCSlib.Complexity.Randomized.SpaceAmplifyPolyCode
import TCSlib.Complexity.Randomized.SpaceAmplifyPolyMachine
import TCSlib.Complexity.Randomized.SpaceAmplifyPolyRun
import TCSlib.Complexity.Randomized.SpaceAmplifyPoly
import TCSlib.Complexity.Randomized.ZeroPReduce
import TCSlib.Complexity.Randomized.BPPAmplify
import TCSlib.Complexity.Randomized.RPExpected
import TCSlib.Complexity.Randomized.BPOperator
import TCSlib.Complexity.Randomized.AlgCircuitExample
import TCSlib.Complexity.Randomized.QuasiPolyHierarchy
import TCSlib.Complexity.Randomized.BPPEqP
import TCSlib.Complexity.Randomized.BPTIMEThreshold
import TCSlib.Complexity.Randomized.Space
import TCSlib.Complexity.Randomized.SpaceAmplify
import TCSlib.Complexity.Randomized.SpaceAmplifyRun
import TCSlib.Complexity.Randomized.RandomWalk
import TCSlib.Complexity.Randomized.RandomWalkHitting
import TCSlib.Complexity.Randomized.RandomWalkPad
import TCSlib.Complexity.Randomized.UPath
import TCSlib.Complexity.Randomized.UPathMachine
import TCSlib.Complexity.Randomized.UPathLoops
import TCSlib.Complexity.Randomized.UPathParse
import TCSlib.Complexity.Randomized.UPathSearch
import TCSlib.Complexity.Randomized.UPathWalk
import TCSlib.Complexity.Randomized.UPathRL

/-!
# Randomized Computation

Arora–Barak Chapter 7 (Randomized Computation): the model-free
probabilistic tools, and the chapter's complexity classes and theorems in
the certificate view of [AB09, Def 7.3], relative to an abstract efficiency
notion (`Randomized.VerifierModel`) standing in for polynomial-time Turing
machines.

## Contents

- `Randomized.SchwartzZippel`: the Schwartz–Zippel lemma in Arora–Barak's
  form ([AB09, Lem 7.5]), restated from Mathlib's
  `MvPolynomial.schwartz_zippel_totalDegree`.
- `Randomized.ErrorReduction`: concentration for i.i.d. Boolean trials (Hoeffding form of the
  Chernoff bound [AB09, Cor A.15]) and the majority-vote error bound that is the calculation
  inside the error-reduction theorem ([AB09, Thm 7.10]).
- `Randomized.Classes`: verifier-style `BPP`/`RP`/`coRP`/`ZPP`
  ([AB09, Defs 7.2/7.3/7.6/7.7]), `ZPP = RP ∩ coRP` ([AB09, Thm 7.8]), and
  error reduction at the class level ([AB09, Lem 7.9, Thm 7.10]).
- `Randomized.Adleman`: `BPP ⊆ P/poly` ([AB09, Thm 7.14]), concluding in
  `Language.InPPoly` from `CircuitComplexity.PPoly`.
- `Randomized.SipserGacs`: certificate-style `Σ₂ᵖ`/`Π₂ᵖ` and
  `BPP ⊆ Σ₂ᵖ ∩ Π₂ᵖ` ([AB09, Thm 7.15]).
- `Randomized.PolyTimeModel`: the instantiation of the abstract verifier
  model by genuine polynomial-time machines (`Complexity.P`), discharging
  the closure hypotheses and connecting `Σ₂` to `Complexity.SigmaP 2`.
- `Randomized.PTM`: probabilistic Turing machines as binary-choice machines read
  probabilistically; `BPTIME`, `BPP_PTM`, `RTIME`, `RP_PTM`, `coRP_PTM`
  ([AB09, Def 7.1, Def 7.2, Def 7.6]).
- `Randomized.Inclusions`: `P ⊆ BPP`, `RP ⊆ NP`, `RP, coRP ⊆ BPP`, `BPP ⊆ EXP`,
  `NP = P ⇒ BPP = P`, `3SAT ∈ BPP ⇒ PH = Σ₂ᵖ` ([AB09, §7.1, §7.3, §7.5.1]) and RP error
  reduction ([AB09, Exercise 7.4]).
- `Randomized.PTMEquiv`: the PTM classes equal the certificate classes over polynomial-time
  verifiers ([AB09, Def 7.2 ≡ Def 7.3]).
- `Randomized.Median`: `FindKthElement` and its expected number of comparisons
  ([AB09, §7.2.1, Claim 7.4]).
- `Randomized.PrimalityMath`, `Randomized.Primality`: Solovay–Strassen; `PRIMES ∈ coRP`
  ([AB09, §7.2.2]).
- `Randomized.AlgCircuit`: algebraic circuits, their polynomials and degree, `ZEROP`
  ([AB09, §7.2.3]).
- `Randomized.RandomBits`: shared counting lemmas over random strings (conditioning on a
  prefix, the union bound) and numbers read off blocks of fair coins.
- `Randomized.Fingerprint`: the fingerprinting test for `ZEROP` and its error analysis
  ([AB09, §7.2.3]).
- `Randomized.ZeroPEval`, `Randomized.ZeroPRun`: the polynomial-time evaluator of encoded
  algebraic circuits modulo `k`.
- `Randomized.ZeroP`, `Randomized.ZeroPPIT`: `ZEROP ∈ coRP` and polynomial identity testing
  in `coRP` ([AB09, §7.2.3]).
- `Randomized.MatchingMath`, `Randomized.Matching`: Edmonds matrix, Lovász's test, bipartite
  perfect matching in `RP` ([AB09, §7.2.4]).
- `Randomized.ExpectedTime`: expected running time, `ZTIME`, `ZPP_PTM`
  ([AB09, §7.3, Def 7.7]) and Markov truncation ([AB09, §7.4.2]).
- `Randomized.Coins`: biased coins from fair coins and von Neumann's extractor
  ([AB09, Lemma 7.12, Lemma 7.13]).
- `Randomized.ZPPEquiv`, `Randomized.ZPPHosts`, `Randomized.ZPPHostsClasses`: `ZPP` in its
  expected-time, abort and certificate forms, and `ZPP = RP ∩ coRP` for Def 7.7
  ([AB09, Theorem 7.8, Exercise 7.6]).
- `Randomized.Reductions`: randomized reductions and `BP·NP` ([AB09, Def 7.16, Def 7.17]).
- `Randomized.NPPoly`: `NP/poly` and `BP·NP ⊆ NP/poly` ([AB09, Exercise 7.7]).
- `Randomized.Yap`: Yap's theorem (`coNP ⊆ NP/poly ⇒ PH = Σ₃ᵖ`) and [AB09, Exercise 7.8].
- `Randomized.DirectedWalk`: the random walk on a directed graph can need Ω(2ⁿ) steps
  [AB09, Exercise 7.10].
- `Randomized.BPPHard`: `⟨M, x, 1ᵗ⟩` with acceptance probability ≥ 2/3 is BPP-hard
  [AB09, §7.5.3, p. 138].
- `Randomized.BPLInPCount`, `Randomized.BPLInPWords`, `Randomized.BPLInP`: `BPL ⊆ P` by an exact
  dynamic program over configurations [AB09, Exercise 7.9].
- `Randomized.RandomWalkCover`: connectivity, bipartiteness and the bipartite double cover for
  regular multigraphs; even-length walks of length `2n` between any two vertices.
- `Randomized.RandomWalkMixing`, `Randomized.RandomWalkMixingPad`: contraction to uniform,
  uniqueness of the stationary distribution, visit frequency, and the self-loop regularization
  transfer [AB09, Exercise 7.11(b), (e)].
- `Randomized.UniformSample`: uniform sampling from `[N]` with coin tosses [AB09, Exercise 7.1].
- `Randomized.BiasedCoin`, `Randomized.BiasedCoinHalting`: ρ-coin PTMs; an uncomputable ρ decides an
  undecidable language in polynomial time [AB09, Exercise 7.5].
- `Randomized.SpaceAmplifyPolyCode`, `…Machine`, `…Run`, `Randomized.SpaceAmplifyPoly`: BPL and RL
  error reduction to `2^{-n^d}` in logarithmic space [AB09, §7.7, p. 139].
- `Randomized.ZeroPReduce`: the polynomial-time reduction PIT ≤ₚ ZEROP and closure of RP/coRP under
  ≤ₚ [AB09, §7.2.3].
- `Randomized.BPPAmplify`: Lemma 7.9 and Theorem 7.10 for polynomial-time PTMs and the
  polynomial-time verifier model; any constant above `1/2` gives BPP [AB09, §7.4.1].
- `Randomized.RPExpected`: expected polynomial time gives the same RP and coRP [AB09, §7.4.2].
- `Randomized.BPOperator`: the `BP·` operator; `BP·P = BPP` and `BP·NP` agrees with Def 7.17
  [AB09, Chapter notes].
- `Randomized.AlgCircuitExample`: `∏(1 + xᵢ)` has a circuit with `2n` operations but `2ⁿ` monomials
  [AB09, §7.2.3, p. 129].
- `Randomized.QuasiPolyHierarchy`: `P ⊊ DTIME(n^{log n})` via a time-constructible quasi-polynomial
  budget.
- `Randomized.BPPEqP`: if `BPP = P` then `BPP ⊊ DTIME(n^{log n})` and BPP has a complete problem
  [AB09, §7.5, §7.5.3].
- `Randomized.BPTIMEThreshold`: any constant threshold in `(1/2, 1)` gives the same
  `BPTIME(T(n))` [AB09, §7.1, p. 125].
- `Randomized.Space`, `Randomized.SpaceAmplify`, `Randomized.SpaceAmplifyRun`: randomized
  space, `BPL`, `RL`, `RL ⊆ NL ⊆ P`, error reduction in log space ([AB09, §7.7, Def 7.18]).
- `Randomized.RandomWalk`, `Randomized.RandomWalkHitting`, `Randomized.RandomWalkPad`:
  random walks on regular multigraphs and their hitting times ([AB09, Exercise 7.11]).
- `Randomized.UPath`, `Randomized.UPathMachine`, `Randomized.UPathLoops`,
  `Randomized.UPathParse`, `Randomized.UPathSearch`, `Randomized.UPathWalk`,
  `Randomized.UPathRL`: `UPATH ∈ RL` ([AB09, Theorem 7.19]).

All entries, and the files they describe, cite the printed book's (2009) numbering.

## References

* [AB09] S. Arora, B. Barak, *Computational Complexity: A Modern Approach*,
  Cambridge University Press, 2009.
-/
