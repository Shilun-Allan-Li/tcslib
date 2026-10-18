/-
Copyright (c) 2026 Seyoon Ragavan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Seyoon Ragavan
-/
import TCSlib.Complexity.FormulaKit.Gate
import TCSlib.Complexity.FormulaKit.Emit

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Complexity — the machine-to-formula kit

Item H6 of the host registry (`machine-library-design.md` §14): closed-form variable
indexing, fixed-arity gates given by explicit truth tables, the size ledgers, and ordered
uniform emission, shared by the reductions that turn a machine into a formula. Its consumers
are the configuration codec of [AB09, Claim 4.4(2)] (`Complexity.ConfigCodec`, in
`ClassPSPACE/TQBF.lean`) with the `TQBF` hardness reduction of [AB09, Theorem 4.13], and,
by a later restyling row, the Cook-Levin reduction (`CookLevin/Hardness.lean`). The companion
item "auxiliary variables after the prefix" lives with the quantified formulas, as
`Complexity.QBF.truth_exSuffix_of_pointwise` (`Formulas/QBF.lean`).

## Contents

* `FormulaKit.Gate` — block variables, truth-table templates and gates, the exactly-one
  gadget, the clause-and-literal cost and the serialization ledger [AB09, Claim 2.13].
* `FormulaKit.Emit` — fragments and the polynomial-time emission of ordered clause groups,
  fixed templates with polynomial-time wires, and variable offsets.

## References

* [AB09] S. Arora, B. Barak, *Computational Complexity: A Modern Approach*,
  Cambridge University Press, 2009. (Lemma 2.11 and Claim 2.13, pp. 45-49; Claim 4.4,
  pp. 80-81; Theorem 4.13, pp. 84-85.)
-/
