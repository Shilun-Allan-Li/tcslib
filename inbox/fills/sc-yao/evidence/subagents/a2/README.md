# Decoder/Alice diagnostic evidence (a2)

The v1 immutable handoff remains unchanged. This directory records whole-file diagnostic
seals and proof-only reader repairs. Every probe uses `-DmaxErrors=0`, the whole imported
TCSlib closure, the shared slot wrapper with tag `sc-yao-a`, and this worktree's own oleans.
The runner counts both `error:` and `error(...)` diagnostic forms, records source hashes,
and preserves source snapshots and complete raw logs before reporting a status.

## Original diagnostic run

`seals/final/manifest.json` names the 40 A/B by strict/coe probes for all ten owned modules.
`probe-runs/seals-01/` preserves their untouched sources and raw results. All ten modules
are absent at the issued base, as recorded in `base-manifest.json`.

Two source dependencies on foreign definitions were identified:

* `Garbling.gateKind_test_poly`: six negative constructor pairs used `rfl` on derived
  decidable equality. Replaced that last step with simplification from public constructor
  equations and constructor disjointness. All other declarations in that file passed.
* `RowFromCoins.rowWord_garbledRow`: the default argument's circuit-size bound relied on
  reducing `DAGCircuit.size`. Added the published `DAGCircuit.size_eq` reader explicitly.

Both changes are proof-only: no statement, executable object, or machine interface changed.
Original source versions remain in the probe snapshots. The gate-kind repair was also
normal-checked independently by the lead before the child repair checks began.

## Repair and control run

`repair-followup-manifest.json` serializes normal checks for the six affected modules,
eight repair seals, eight positive/negative seal controls, and a complete stored-constant
axiom and transitive admission trace. `seals/final-repair01/` contains the repaired probes;
no original diagnostic probe was overwritten.

The negative controls deliberately read `TCSlib.Cryptography.uprob` through its implementation;
exactly one error per sealed control is expected. Unsealed controls must pass. The axiom
probe lists every stored constant whose home module is one of the ten owned modules,
including private/generated declarations, along with all axioms and the complete set of
transitively used declarations containing `sorryAx`.

## Fake-program reuse search

The subsequent fake-program construction will reuse `rowWordWith` and `tableWordWith`.
Before adding tuple/concatenation glue, the search found the public
`FunFamily.ofFn_blocks_symm` (Asymptotic/OneWay.lean:380),
`EnsembleLemmas.ofFn_blocks_symm` (EnsemblesLemmas.lean:433),
`MultiMsg.flatMap_ofFn` (FromPRF/ReductionMachine.lean:665), and Mathlib `List.ofFn_mul`.
The existing approved `ColMachines.polyTimeComputable_flatMap_range` supplies the loop.
No new proof of the finite-product or flatten identity is needed.

## Completed outcome

All forty final seal variants pass: thirty-two untouched original probes plus eight
repaired probes. All six affected normal checks pass. The four positive controls pass;
the four deliberately sealed negative controls each fail with exactly one error. The
complete trace reports 172 stored constants, no transitive `sorryAx` closure, and only
`propext`, `Classical.choice`, and `Quot.sound` as axioms. See `audit-summary.json`,
`final-seal-results.json`, and the complete raw trace for the mechanically recorded evidence.
