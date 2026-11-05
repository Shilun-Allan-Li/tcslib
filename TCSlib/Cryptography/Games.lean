/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TCSlib.Cryptography.Games.OracleComp
import TCSlib.Cryptography.Games.Probability
import TCSlib.Cryptography.Games.Simulate
import TCSlib.Cryptography.Games.Advantage
import TCSlib.Cryptography.Games.Hopping
import TCSlib.Cryptography.Games.Protocols

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Security games and protocols as oracle computations

One framework for the security games and the two-party protocols of [PS10] chapters 5–8:
- oracle computations, a free monad over an indexed family of oracles;
- uniform sampling as an oracle, with a real-valued, finite-sum probability;
- stateful oracle implementations with query logging, and simulation;
- the shapes of security advantages;
- the game-hopping lemmas;
- two-party executions.

It lives in the namespace `TCSlib.Cryptography.Games`. Its connections to the ch. 2–4 layer are
the next layer (S2b): the concrete layer's `QueryTree` and `uprob`, the machine model `NUPPT`, and
the interaction model `Strategy`.

## Contents

* `TCSlib.Cryptography.Games.OracleComp`: oracle specifications, oracle computations, unions,
  query costs.
* `TCSlib.Cryptography.Games.Probability`: the sampling oracle, expectations, probabilities,
  output distributions.
* `TCSlib.Cryptography.Games.Simulate`: oracle implementations, simulation, logging, composition.
* `TCSlib.Cryptography.Games.Advantage`: acceptance, distinguishing and guess-the-bit
  advantages, the hybrid argument.
* `TCSlib.Cryptography.Games.Hopping`: the difference lemma, identical until bad, the collision
  bound.
* `TCSlib.Cryptography.Games.Protocols`: parties, the message exchange, executions with D8's
  reading of the end, and traced executions recording views.

## References

* [PS10] R. Pass, a. shelat, *A Course in Cryptography*, lecture notes, 3rd ed., January 2010.
* [VCVio] D. Tuma and the VCVio contributors, *VCVio: machine-checked cryptographic proofs in
  Lean*, https://github.com/dtumad/VCV-io, commit 9054989327a7185ff19ef9ff0f119cccea479501
  (2026-11-04), Apache License 2.0. Design adapted (no code transcribed): oracle specifications
  indexed by a type of oracle names (`VCVio/OracleComp/OracleSpec.lean`), oracle computations as
  a free monad over them (`OracleComp.lean`, `OracleQuery.lean`), probabilistic computations as
  computations over the uniform-selection oracles (`OracleComp/ProbComp/Basic.lean`), and
  simulation of oracles by stateful handlers with query logging and composition (`SimSemantics/`,
  `SimSemantics/QueryImpl/Compose.lean`, `QueryTracking/LoggingOracle`).
* [BR06] M. Bellare, P. Rogaway, *The security of triple encryption and a framework for
  code-based game-playing proofs*, EUROCRYPT 2006.
* [Sho04] V. Shoup, *Sequences of games: a tool for taming complexity in security proofs*, IACR
  ePrint 2004/332.
-/
