/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TCSlib contributors
-/
import TCSlib.Cryptography.ZeroKnowledge.Encoding
import TCSlib.Cryptography.ZeroKnowledge.Interaction
import TCSlib.Cryptography.ZeroKnowledge.InteractiveProofs
import TCSlib.Cryptography.ZeroKnowledge.Defs
import TCSlib.Cryptography.ZeroKnowledge.GraphIsomorphism
import TCSlib.Cryptography.ZeroKnowledge.GraphIsomorphismZK
import TCSlib.Cryptography.ZeroKnowledge.Commitment
import TCSlib.Cryptography.ZeroKnowledge.ThreeColoring
import TCSlib.Cryptography.ZeroKnowledge.NP
import TCSlib.Cryptography.ZeroKnowledge.Encryption

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Zero knowledge

Chapter 4 of [PS10] (*Knowledge*): interactive protocols and proofs, zero-knowledge in its
honest-verifier, general, statistical and perfect forms, and the applications — zero-knowledge
encryption, the graph non-isomorphism and graph isomorphism protocols, commitments from
one-way permutations, and zero-knowledge proofs for graph 3-colouring and hence for every
language with a Levin reduction to it. The model is the next-message-function model of the
campaign's foundation decision D8 (`PassShelatChapter2-4Plan.md`): strategies are
next-message functions with explicit polynomial random tapes, protocols have a fixed
polynomial number of messages, efficient parties are uniform `Complexity.NUPPT`s, simulators
are strict PPT, and the rewinding simulators of the text are truncated so that the
zero-knowledge theorems are statistical (D8, D10).

## Contents

* `Encoding` — string encodings of graphs, permutations and `3`-colourings with their total
  decoders, the coin table feeding the rejection-sampled permutation, and the polynomial-time
  statements of the honest parties' string operations (Inf-4.1, Inf-4.2).
* `Interaction` — next-message strategies, executions, views, transcripts and outputs
  [PS10, §4.4] (Def-114.a – Def-116.b).
* `InteractiveProofs` — interactive proof systems, soundness error, witness relations and
  interactive proofs with efficient prover [PS10, Definitions 116.1, 119.5, 191.11]; the
  one-message witness protocol as the sanity theorem (Def-116.1, Def-117.a, Def-119.5,
  Def-191.11).
* `Defs` — honest-verifier, general, statistical and perfect zero-knowledge
  [PS10, Definitions 121.1, 121.2], the implications between them, and negligibility in the
  instance length (Def-121.1, Def-121.2, Def-122.a, Inf-4.4).
* `GraphIsomorphism` — the graph non-isomorphism and graph
  isomorphism protocols with their completeness and soundness [PS10, Protocols 118.3 and
  120.6, Propositions 118.4 and 120.7].
* `GraphIsomorphismZK` — the truncated simulator and statistical
  zero-knowledge of the graph isomorphism protocol [PS10, Theorem 122.3, Algorithm 123.4].
* `Commitment` — commitment schemes and their construction from a
  one-way permutation with a hard-core predicate [PS10, Definition 126.3, Theorem 126.4].
* `ThreeColoring` — the zero-knowledge protocol for graph 3-colouring [PS10, Protocol 127.5,
  Propositions 127.6 and 128.8] (a sub-facade over `ThreeColoring/{Language,Protocol,Simulator}`).
* `NP` — Levin reductions and zero-knowledge proofs for NP
  [PS10, Theorem 124.1].
* `Encryption` — zero-knowledge encryption and its equivalence with
  single-message security [PS10, Definition 111.1, Theorem 112.2].

## References

* [PS10] R. Pass, a. shelat, *A Course in Cryptography*, lecture notes, 3rd ed., January 2010.
  (Chapter 4, Knowledge.)
-/
