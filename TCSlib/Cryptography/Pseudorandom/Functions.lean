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
import TCSlib.Cryptography.Pseudorandom.Functions.Asymptotic.Defs
import TCSlib.Cryptography.Pseudorandom.Functions.Asymptotic.GGM
import TCSlib.Cryptography.Pseudorandom.Functions.Asymptotic.GGM.Evaluator
import TCSlib.Cryptography.Pseudorandom.Functions.Asymptotic.GGM.Reduction
import TCSlib.Cryptography.Pseudorandom.Functions.Asymptotic.GGM.Run

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Pseudorandom functions

The finite oracle games and Goldreich–Goldwasser–Micali construction come
from [Gar26, §3.4]. The asymptotic contracts quantify over polynomial-time
machines and polynomial query budgets [PS10, Definitions 96.1 and 96.2].

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
* `Functions/Asymptotic/Defs.lean` gives the oracle ensemble and PRF contracts.
* `Functions/Asymptotic/GGM.lean` proves the asymptotic PRG-to-PRF implication.
* `Functions/Asymptotic/GGM/Evaluator.lean` implements the tree walk.
* `Functions/Asymptotic/GGM/Reduction.lean` implements the lazy table and reduction.
* `Functions/Asymptotic/GGM/Run.lean` gives the machine and its run agreement.

## References

* [PS10] R. Pass, a. shelat, *A Course in Cryptography*, lecture notes, 3rd ed.,
  January 2010, §3.8.
* [Gar26] S. Garg, *A Course in Theory of Cryptography*, lecture notes, UC Berkeley,
  draft of 22 January 2026, §3.4.
-/
