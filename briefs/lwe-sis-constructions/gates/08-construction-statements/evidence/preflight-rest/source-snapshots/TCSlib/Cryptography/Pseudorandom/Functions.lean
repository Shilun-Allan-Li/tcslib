/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TCSlib contributors
-/
import TCSlib.Cryptography.Pseudorandom.Functions.OracleAdversary
import TCSlib.Cryptography.Pseudorandom.Functions.LazySampling
import TCSlib.Cryptography.Pseudorandom.Functions.Defs
import TCSlib.Cryptography.Pseudorandom.Functions.SubHybrids
import TCSlib.Cryptography.Pseudorandom.Functions.GGM

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Pseudorandom functions

Concrete-layer formalization of [Gar26, §3.4]: adaptive oracle adversaries, pseudorandom
functions, and the Goldreich–Goldwasser–Micali construction from a length-doubling
pseudorandom generator.

## Contents

* `Functions/OracleAdversary.lean`: adaptive oracle adversaries as query trees, their
  evaluation, query bounds and oracle simulation.
* `Functions/LazySampling.lean`: lazy sampling of a random oracle and its equivalence with
  a uniform random function; probability helpers.
* `Functions/Defs.lean`: keyed function families, random functions and the PRF advantage
  (Definitions 3.6–3.9).
* `Functions/SubHybrids.lean`: a table of PRG outputs against an adaptive `q`-query
  adversary (the sub-hybrids of the GGM proof).
* `Functions/GGM.lean`: the GGM construction and its security (Construction 3.3,
  Theorem 3.3).

## References

* [Gar26] S. Garg, *A Course in Theory of Cryptography*, lecture notes, UC Berkeley,
  draft of 22 January 2026, §3.4.
-/
