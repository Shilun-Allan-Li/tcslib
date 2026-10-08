/-
Copyright (c) 2026 Seyoon Ragavan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Seyoon Ragavan
-/
import TCSlib.Complexity.TuringMachine.OracleAgreement
import TCSlib.Complexity.Diagonalization.EXPCOM
import TCSlib.Complexity.Diagonalization.Relativization
import TCSlib.Complexity.Diagonalization.NotTimeConstructible

/-!
# Diagonalization: relativization and its limits

[AB09, §3.4]: the Baker-Gill-Solovay relativization theorem and its
supporting cast. The headline results are `Complexity.baker_gill_solovay`
(oracles `A`, `B` with `P^A = NP^A` and `P^B ≠ NP^B` — [AB09, Theorem 3.7],
[BGS75]), the `EXPCOM` identities `Complexity.POracle_EXPCOM_eq_EXP` /
`Complexity.NPOracle_EXPCOM_eq_EXP` ([AB09, Example 3.6(3)]), and the
non-time-constructible function `Complexity.exists_not_timeConstructible`
([AB09, Exercise 3.5]).

## Contents

- `TuringMachine.OracleAgreement` (the locality layer, housed with the oracle
  machine model): submitted-query lists `queriesWithin`/`queriesAlong`, and
  agreement of runs under oracles that agree on the queries (deterministic
  and nondeterministic, length-locality and query-set forms)
- `Diagonalization.EXPCOM`: the `EXPCOM` oracle and the chain
  `EXP ⊆ P^EXPCOM ⊆ NP^EXPCOM ⊆ EXP` with its three identities
- `Diagonalization.Relativization`: the unary witness language `U_B`,
  `U_B ∈ NP^B`, the extrinsically clocked enumeration of deterministic
  finite oracle machines, the stage construction, and Theorem 3.7
- `Diagonalization.NotTimeConstructible`: a function dominating the identity
  that is not time-constructible

## References

* [AB09] S. Arora, B. Barak, *Computational Complexity: A Modern Approach*,
  Cambridge University Press, 2009. (§3.4.)
* [BGS75] T. Baker, J. Gill, R. Solovay, *Relativizations of the P =? NP
  question*, SIAM Journal on Computing 4(4), 1975.
-/
