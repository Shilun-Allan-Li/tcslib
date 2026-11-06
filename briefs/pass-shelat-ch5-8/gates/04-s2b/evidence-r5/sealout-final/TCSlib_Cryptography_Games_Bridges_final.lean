/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TCSlib.Cryptography.Games.Machines
import TCSlib.Cryptography.Games.BitCodec
import TCSlib.Cryptography.Games.Efficiency
import TCSlib.Cryptography.Games.Bridges.QueryTree
import TCSlib.Cryptography.Games.Bridges.Experiments
import TCSlib.Cryptography.Games.Bridges.Machines
import TCSlib.Cryptography.Games.Bridges.Strategies

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false
-- (no candidates)

/-!
# The `Games` framework, connected to machines and to the ch. 2–4 layer

The core framework (`TCSlib.Cryptography.Games`) needs only Mathlib and finite distributions. This
facade adds the layer (S2b of the Pass–shelat ch. 5–8 campaign) that connects it to the machine
model and to the ch. 2–4 layer.

## Contents

* `Games.Machines`: machines as oracle computations (`NUPPT.toComp`, `NUPPT.toCompOn`).
* `Games.BitCodec`: bit-string oracles and their machine codec (`bitSpec`, `bitCodec`).
* `Games.Efficiency`: polynomial-time handlers (adversary input, queries, finalization) and the
  efficiency targets T1 and T2, with their companions (adversaries without input; T4, the bridge
  to the ch. 2–4 next-query machines) (the efficiency fill).
* `Games.Bridges.QueryTree`: the concrete layer's query trees, which *are* one-oracle computations
  (item F-1); their evaluation, simulation and query bounds are the framework's.
* `Games.Bridges.Experiments`: the concrete layer's experiments (`invProb`, `predProb`,
  `acceptProb`, `distAdv`) as games (bridge B2).
* `Games.Bridges.Machines`: the ch. 2–4 next-query machines as an instance of the decoder (B3).
* `Games.Bridges.Strategies`: next-message strategies embedded as parties; the embedded
  execution is D8's (B4).
-/
