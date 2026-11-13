/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TCSlib.Cryptography.Encryption.PublicKey.NonMalleability.Simulation.Generic

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Coin strings of the IND ⇒ SIM machines

A local fact used by the two machines of direction IND ⇒ SIM of [PS10, Theorem 174.8] (the
simulator and the NM adversary): a machine's coin string has `coins(n)` bits
(`length_ofFn_coins`).

The generic facts first proved here now live in shared modules: the readers of a round input are
`Games.InteractiveHandler.rU`, …, `rAns`; the calls and finalizations whose rounds return at once
or after one outer query are `Games.InteractiveHandler.impl_of_ret_padFin`,
`impl_of_query_padFin` and `finish_of_ret_padFin`; the cost of a one-shot oracle is
`Games.simulate_costBoundedBy_once`; the split of a padded concatenation is
`Games.padFin_append_split`; the seeds made of coins are `EnsembleLemmas.seedEquiv` and
`EnsembleLemmas.seedEquivPoly`.

## Main results

* `NMSim.length_ofFn_coins`.

## References

* [PS10] R. Pass, a. shelat, *A Course in Cryptography*, lecture notes, 3rd ed., January 2010,
  Theorem 174.8 (book p. 174).
-/

namespace TCSlib.Cryptography.Composability.NMSim

open Complexity Turing TCSlib.Cryptography TCSlib.Cryptography.Games

/-- A machine's coins have `coins(n)` bits: `|⟦r⟧| = A.coins.eval n`. -/
theorem length_ofFn_coins (A : NUPPT) (n : ℕ) (r : A.Coins n) :
    (List.ofFn r).length = A.coins.eval n := by
  rw [List.length_ofFn, NUPPT.coinLen_eq]

end TCSlib.Cryptography.Composability.NMSim
