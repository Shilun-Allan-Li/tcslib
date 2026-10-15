# Machine-routine layer (§12) — audit loop resolutions

**Gate: CLOSED (round 3, 2026-10-09).** Three rounds:

| Round | Verdict | Findings files |
|---|---|---|
| 1 | FAIL — 0 blockers, 4 majors, 3 minors, 3 notes | `audits/routine-infra-findings.md` |
| 2 | FAIL — 1 blocker, 0 majors, 0 minors, 1 note | `audits/routine-infra-r2-findings.md` |
| 3 | **PASS — 0 blockers, 0 majors, 1 minor, 0 notes** | `audits/routine-infra-r3-findings.md` |

## The loop

* **Round 1** (audited surface: the 47-statement skeleton of
  `Build/{Embed,Seam,Catalog}.lean`) found no counterexample to any of the
  47 sorried conclusions but four interface majors: the closed embeddings
  cannot express the halt-to-live return (R1 — the final halting emission
  is lost to the halt or to premature seam dispatch, formal trace
  supplied); the seam theorems were canonical-`Cfg.ofWords`-only (R2); the
  first-return cut excluded positive entry-equals-exit calls (R3); and
  `pairMapSnd`'s documented witness was refuted — its capture tape visits
  output-length cells (R4). Repairs added **three definitions and nine
  sorried contracts** (the returning embeddings
  `embedSilentRetTM`/`embedEmitRetTM` with through-halt run and visited
  contracts; the general-configuration seam theorems
  `seamCompTM_{run,firstReturn,visitedByTapeHead}_ofCfg`; the
  `seamReleaseTM` adapter with first-return and visited contracts),
  commissioned the forwarding `pairMapSnd` controller, and corrected the
  `polyBits`/`compare`/`increment` sketches (R5-R7) plus the
  R8/R9/R10 descriptions. 47 → 56 sorried statements.
* **Round 2** accepted seven of the nine new contracts, every round-1
  disposition, and the S7/S8/S9 replays — but found both through-halt
  contracts **false at `T = 0`** for an initially halted configuration
  (the handover projection demands `none = some (Sum.inr ())`). Repair:
  `(hc : c.state ≠ none)` on both.
* **Round 3**: PASS. The auditor replayed the counterexample against the
  amendment (no instance exists), proved the full positive-time induction
  through the final step, verified consumers discharge `hc` at every
  advertised live seam, and confirmed byte-identity of everything else
  down to blob hashes.

## Minor, swept in the closing commit and re-verified

| # | Sweep |
|---|---|
| R3-1 | The handover docstring's equivalence is now stated under **both** first-halt hypotheses (`hc ↔ 0 < T` needs `hhalt` forward and `hlive 0` backward); the round-3 pack's `hhalt`-only phrasing is acknowledged below |

## Pack errata, acknowledged (shipped packs are never edited)

* Round-2 pack: the new-contract subdivision read "six run/first-return
  plus three visited-set"; the correct split is **five and four**
  (round-2 note R2-2).
* Round-3 pack: the brief repeated the `hhalt`-only equivalence
  qualification corrected by R3-1.

## Carried into the fill briefs

* The round-2/round-3 positive-time through-halt induction (step 3's
  component check, the `Option.elim` successor equations, the last-step
  case) — effectively a proof plan for both `_run` contracts.
* The commissioned `pairMapSnd` forwarding controller with the
  coefficient-one payload ledger (round-2's R4 calculation); the
  `polyBits` case split; the exact `compare`/`increment` counts.
* Round-1's S1-S12 sanity list (S7/S8/S9 already replayed by the
  auditors); the loop-row sibling contracts (R10) and the zone/virtual
  input consumer layers (R9) as commissioned future work.
* `Catalog.lean` at 1012 lines: justified by the queued per-theme split
  (backlog §2, decision 12.2 option (c)).

## Consequences

* **Every statement gate of the chapters-3-4 campaign is now CLOSED**:
  P0, P3.1, P3.2, P3.3, P4.1, P4.2, P4.3, P4.4, and §12.
* The §12 freeze lifts: `Build/{Embed,Seam,Catalog}.lean` join the
  `TuringMachine.lean` facade and the root's temporary imports are
  removed (the closing commit).
* The P4.1-carried `NP ⊆ PSPACE` hard dependency and the P4.2/P4.3
  fill-engine references now rest on a **closed** §12 surface.
* Statement-freeze baseline: the closing commit.
