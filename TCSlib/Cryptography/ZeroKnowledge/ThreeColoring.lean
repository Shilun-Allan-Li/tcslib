/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TCSlib contributors
-/
import TCSlib.Cryptography.ZeroKnowledge.ThreeColoring.Language
import TCSlib.Cryptography.ZeroKnowledge.ThreeColoring.Protocol
import TCSlib.Cryptography.ZeroKnowledge.ThreeColoring.Simulator

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Zero-knowledge for graph 3-colouring

The zero-knowledge proof for the language of 3-colourable graphs [PS10, §4.7.2]: the
language and its witness relation (Def-124.f), the protocol of [PS10, Protocol 127.5] built on
a commitment scheme of `ZeroKnowledge/Commitment.lean`, its completeness and soundness
[PS10, Proposition 127.6], and the simulator of [PS10, Algorithm 128.7] with
[PS10, Proposition 128.8]. The protocol is the step 1 of [PS10, Theorem 124.1]; step 2 (every
language with a Levin reduction to `3COL`) is `ZeroKnowledge/NP.lean`.

## Contents

* `Language` — 3-colourings, the language `3COL` and its witness relation `R_3COL`, the edge
  enumeration, the bound `(1 - 1/m)^{nm} ≤ e^{-n}` (Claim-125.a), colours as `n`-bit committed
  values and the rejection samplers of the honest parties (Def-124.f, Claim-125.a, DQ4, D10).
* `Protocol` — the commitment, challenge and opening messages, the verifier's check, one
  iteration and the `n|E|`-fold protocol (Prot-127.5), completeness (Claim-127.e), the
  committed colouring and its bad edge (Lem-127.f), adaptive sequential soundness
  (Lem-127.g, Claim-127.h), and the interactive-proof half of [PS10, Proposition 127.6]
  (Prop-127.6).
* `Simulator` — the distinct colour pairs and `S₃ ≃ ColorPair` (Lem-129.b), the typed views
  and the attempts of `S`, `S'`, `S''` (Alg-128.7, Claim-129.a, Claim-129.c), the hybrid
  reduction to multi-value hiding (Claim-129.d), the string simulator and its efficiency
  (Claim-128.a), and [PS10, Proposition 128.8] with the assembled [PS10, Proposition 127.6]
  (Prop-128.8, Prop-127.6).

## References

* [PS10] R. Pass, a. shelat, *A Course in Cryptography*, lecture notes, 3rd ed., January 2010.
  (§4.7.2, pp. 127–129.)
-/
