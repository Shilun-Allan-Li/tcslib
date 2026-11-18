# Deterministic bounded simulation proof draft

Target: FunctionalEncryption/Run.lean, simulate_buildComp_detImpl_eq_pure.
The .lean.inc file is the EXACT live theorem header followed by its replacement proof.
Keep the existing proof-sketch docstring. It belongs in the original namespace and existing
variables context, with Games open; no import, helper, statement or algorithm changes.

Status: DRAFT_UNELABORATED. One tactic block, no admissions. No live edit, Lean/lake/build
or Git command was run. Root must elaborate and run the required source-bound checks.

Proof: induction on the query budget, generalizing history/state. At zero budget, split the
next Move; use the corresponding buildComp/runDet readers and simulate_pure. At positive
budget, a return is immediate. A query uses buildComp_succ_of_query and runDet_succ_of_query,
then simulate_query, detImpl_apply and pure_bind. The resulting goal is the induction
hypothesis at the identical appended answer and updated state. No foreign body is unfolded.

Actual searches/reads, before drafting:

- rg `theorem simulate_pure|theorem simulate_query|theorem pure_bind|theorem
  buildComp_(zero|succ)_of` in Games/{Simulate,OracleComp,Machines}.lean.
- rg `simulate.*detImpl|simulate_buildComp|simulate.*runDet|buildComp.*simulate`
  throughout live TCSlib. Only the existing admitted target, its consumers, and specialized
  machine/interactive implementations were found; no preexisting general stateful theorem.
- Read the full current Run.lean to preserve exact signature and case-reader argument order.
- Read Games/Simulate.lean:65-108; OracleComp.lean:108-122; Machines.lean:124-155.
- Read Games/Efficiency/Handler.lean:486-505 as the nearest existing query proof pattern.
  Its larger hRaw_spec is machine-specific, and is NOT copied as a new helper.
- rg `simulate_ofComp_pure|evalFn.*simulate|simulate.*pure.*evalFn` in
  Games/Bridges/QueryTree.lean. simulate_ofComp_pure is deterministic STATELESS simulation
  of a supplied query tree, whereas this target threads a changing σ and bounded history.

Published dependencies used:

- Games.buildComp_zero_of_ret :128, _zero_of_query :134,
  _succ_of_ret :140, _succ_of_query :148 in Machines.lean.
- Games.simulate_pure :93, simulate_query :97 in Simulate.lean (impl is first explicit arg,
  inferred by rw from the target, as in the existing Handler query pattern).
- Games.OracleComp.pure_bind :115 in OracleComp.lean.
- Run.detImpl_apply :53, runDet_zero_of_ret :78, _zero_of_query :83,
  _succ_of_ret :88, _succ_of_query :94 (the new helper definitions are not unfolded).

Exact?/apply? probes remain root-only and were not run. No false or unprovable statement
was identified: buildComp's zero-budget return behavior exactly matches runDet's cases.
