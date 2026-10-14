# MIG-1 statement gate: resolutions (rounds 1 and 2; gate CLOSED)

**Gate:** MIG-1, named public witnesses for the existential machine rows of eight library files,
with the deletion of Catalog's 304 private `f2_` copies (`audits/mig1-statements-pack.md`; round
2: `audits/mig1-statements-r2-pack.md`).

- **Round 1** (`audits/mig1-statements-findings.md`, verbatim): **0 blockers, 1 major, 3 minors;
  open.** No public statement was false and no witness body differed from its source. The major
  (finding 1): the deletion plan retargeted the extended loop contract's preparation step at a
  lemma without the fuel-head clause the contract consumes. The round-1 resolutions are the
  round-2 pack's "Resolutions" section (findings 1–4) and its user decisions of 2026-10-14 (all
  five open questions as recommended).
- **Round 2** (`audits/mig1-statements-r2-findings.md`, verbatim; bundle SHA-256
  `6acaad71a9bea8fb60a1b9008a41634cb079392f7df77021b24bac6d7bce1bd0`, 115 sections): **0 blockers,
  0 majors, 3 minors. The gate closes.** Round 1's major is repaired: Loop's private
  `loopHost_prepare` carries the fuel-head clause for both forwarding modes, and the full-file
  overlay proves the extended contract and the public budget theorem over surviving home
  declarations only. No other weaker or inaccessible retarget was found.

## Round-2 findings

| # | Severity | Finding | Resolution |
|---|---|---|---|
| R2-1 | minor | The runner's input precheck omits the worktree sources `build_unit.py` reads (e.g. `Build/Loop.lean`, the H2 draft), so a missing source exits 1 after creating outputs, not 2 before writing | **Recorded for the landing.** The S landing's check scripts precheck every source path before any output is created, with a missing-source negative control. The round-2 evidence stays as committed; its guarantee is read as covering the listed gate inputs only. |
| R2-2 | minor | The retarget negative control compares the *set* of failing examples, not their multiplicities, and does not check the tip control's exit status | **Recorded for F-C's fill gate.** Its checker requires exactly one error in each expected example, no others, and the expected nonzero exit status, with the auditor's duplicate-diagnostic control. The recorded run itself has exactly two errors and exit 1, as the auditor confirms. |
| R2-3 | minor | "174 citations are accessible now" hides that six head-bound retargets need MIG-0b's interval theorem in `Finite` | **Resolved by landing order.** MIG-0b landed (PR #90, 2026-10-14), so `MultiTapeTM.workTapePos_runFrom_mem_Icc` is in `Finite` at the tip. The six retargets are accessible there, and the three `Fin.sum_univ_add` retargets after F-A's Mathlib import. S's re-measurement records both prerequisites explicitly. |
| N1–N8 | notes | No findings: the repair, the seven reviewed statements, the overlay's fidelity, the retarget population, the deletion inventory and decisions, the builder and bundle, the unchanged statement surface, the sequencing | Kept. The obligations they restate stay where the pack placed them (below). |

## Obligations carried to the landing (from the notes and the attestation table)

- **Re-measure at S's actual base:** names, import closures, replay lists, line positions and
  consumers. The post-measurement claims in the round-2 pack's maintainer note (H2-M's shift of
  the R3 site to `CodeSimulator.lean:1282`; the ARM merge's two citations of
  `computesFunInTime_lengthBits`; the 706-module graph) were not verifiable from the packet and
  stay maintainer attestations until then.
- **The head bound:** drop the overlay's stand-in and cite MIG-0b's
  `workTapePos_runFrom_mem_Icc`; H2's `abs_workTapePos_runFrom_sub_le` is a corollary beside it,
  not a MIG-1 landing name (70 public names land).
- **F-C:** compile and replay the strengthened preparation, the moved contract and the budget
  family in `Build/Loop.lean` itself; the overlay is the pre-landing check, not the landing.
- **F-D:** refresh or remove `RAMSimulation/WordSize.lean:75`'s line reference to
  `Build/Catalog.lean:4318`, which the region deletion invalidates.
- **Order:** the B6 hosts land first, because they also edit `TuringMachine/Encoding.lean`, one of
  MIG-1's files. MIG-1 S follows at that tip.
