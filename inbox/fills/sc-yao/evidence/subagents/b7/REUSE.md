# Uniform selected-step security: reuse and ownership

Agent b contributes only SelectedStepChoices and SelectedStepSecurity. The former fixes
all finite reduction data before the distinguisher; the latter consumes actual B1 and the
proved reconstruction, sampling-law and averaging contracts. It introduces no new semantic
garbling, protocol, view, circuit model, probability law, or traversal host.

## Public contracts reused

- Selection/wire uses GateOccurrences.selected_wire_lt and DAGCircuit.size_eq. It names
  an actual argument's Fin vertex; it does not re-prove acyclicity or assume nonempty gates.
- Canonical rows name the same Finset.univ.toList enumeration published by
  GateHybrids.tableWith_eq. Completeness and Nodup are direct transports of Mathlib's
  Finset.mem_toList/mem_univ and nodup_toList; no enumeration/cardinality proof is copied.
- Capacity composes GateOccurrences.length_occurrences_le, size_eq and slotBudget_eval.
  The same reader composition appeared inline in SelectedAdviceBounds.sample_advice_budget;
  its existing conclusion is an advice length bound, not a reusable capacity theorem.
- Offsets, lengths, side messages and advice are finite option selectors over the existing
  SelectedPlan objects. They do not copy the hybrid table or view definitions. None uses
  empty advice, zero offsets/lengths and empty messages, retaining the complete baseline
  tape in every choice. This supplies Nonempty without any input/gate/vertex inhabitant.
- fits consumes SelectedPlan.slots_fit. advice_budget consumes the full closed
  SelectedAdviceBounds.sample_advice_budget. rebuild_some consumes SelectedStep.reconstruct
  plus the wire/capacity/row readers; every structural premise is discharged there.
- filled_negligible directly applies SliceReduction.reconstruction_negligible with
  SliceReconstruction.rebuild_poly. No maximizing, hardwiring, reduction-machine, or
  negligible-bound argument is reproduced. Its nonnegative bound is obtained from the
  existing absolute-value definition of advantage at the always-present None choice.
- selected_negligible directly applies SliceReduction.distAdv_fibers_le and root's
  SelectedLaw.acceptProb_fill separately to the two sample endpoints. It does not re-prove
  independence, uniformity, finite-coordinate exchange, averaging, or hybrid summation.
  All actual tape shifts and unused coordinates retain their original distribution.
- a owns GateHybridChain and the thin headline GateHybridSecurity wrapper. b provides a
  stronger actual-argument bound (all actual p, no additional p.val<2 premise). Thus the
  chain's p.val<2 premise is simply ignored when this bound is instantiated.

The nearest unmerged probability relatives are c's TapeValues and a's CoordinateSwap,
consumed solely through root's public SelectedLaw. No sc-garble/sc-ot/sc-compose probability
proof, sampler, or model definition is copied. The only new Mathlib import is
Data.Fintype.Sigma, already in the approved/seeded closure used by SelectedLaw.

Searches inspected current TCSlib and Mathlib for existing argument/row/tape selectors,
probability/advantage lemmas, PTC rebuilding and the existing finite-advice framework before
implementation. The relevant source search output and root seed ledger/history are preserved.

## Scope and mathematical boundary

The circuit family and all leaf maps, slice plans and advice maps are fixed before D.
Input options need only be finite; no computability or Nonempty assumption on inputs is
introduced. E2 is the sole reconstruction PTC premise, discharged by the actual uniform
leaf implementation at integration. E1 only precomputes fixed messages/advice. B1 is the
explicit SliceMultiMessageSecure G hypothesis; the final caller supplies its frozen
sliceMultiMessageSecure_of_prfOut proof. Joint output length at least 7n+2, concatenation
and E1/E2 canonical evaluation equations are explicit, not hidden sampler assumptions.

All four addressed seed readers are explicit in selected_negligible. The output is one
nonnegative negligible function uniformly bounding every actual selected neighboring step
of the actual uniform-tape GateHybridMessage.sample. No sampler identity, PTC hypothesis,
permutation-uniformity premise, key-value inequality, or positive-size hypothesis remains.

## Development diagnostics

choices-03 exposed an unreduced constant-zero lambda in omega's input. choices-04 normalizes
that core application explicitly and all subsequent checks pass. choices-01/02 and the
complete two security theorems otherwise passed their initial checks. All raw logs remain;
both error: and error(...) diagnostic forms are counted. Old root-owned dependencies replaced
by the parent's SelectedLaw seed are preserved under seed-history; they are not b contributions.
