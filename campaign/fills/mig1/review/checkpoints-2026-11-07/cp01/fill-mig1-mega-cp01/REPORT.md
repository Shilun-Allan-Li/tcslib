# MIG-1 megafill — checkpoint cp01 (F-A, first same-home group) — PARTIAL

Agent: Claude (Anthropic). Branch `fill/mig1-mega`, created at exactly
`83ac315ed9e7089466bd16a32f3b71fbadc556d2` (records/brief `7df0d047d501a1d08982d17d20208faf49d39131`).
Head of this checkpoint: see `HEAD.txt` / `COMMITS.txt`. Verdict: **partial (checkpoint)**.

## Checkpoints reached
- cp01: F-A same-home group — Composition (`idTM_computes`, `ifEqTM_computes`,
  `condTM_computes_iff`) and Encoding (`pairDiagTM_computes`), with their existential rows
  re-pointed and MIG-24 T4 (buffered-composition corollaries) done.

## Target status (17 + 3)
| Target | Status at cp01 |
|---|---|
| `Turing.FinTM.idTM_computes` | proved; axioms standard |
| `Turing.FinTM.ifEqTM_computes` | proved; axioms standard |
| `Turing.FinTM.condTM_computes_iff` | proved; axioms standard |
| `Turing.pairDiagTM_computes` | proved; axioms standard |
| `branchTM_spaceUsed`, `timedCondTM_computes`, `timedCondTM_spaceUsed`, `lengthBitsTM_computes`, `lengthBitsTM_spaceUsed` | open at this checkpoint (sorry) — next commit |
| 5 Loop specs, 3 Primitives specs, 3 forwarding exports | not started |

Remaining exact obligations: the 13 other target admissions listed in
`inputs/target-admissions.json`, the three forwarding exports, F-D retirements.

## Changed public proofs (bodies only; statements frozen)
`computesFunInTime_id`, `computesFunInTime_ifEq`, `exists_cond` (now corollaries of the specs),
`exists_comp_partial`, `computesFunInTime_comp`, `exists_comp_on_image` (MIG-24 T4: corollaries
of `bufferedCompTM_computes_iff`, `_computesFunInTime`, `_on_image`),
`computesFunInTime_pairEncode_diag`.

## Fresh runs (this session) included in `evidence/logs/`
- packet: `packet-extract.log` (bundle SHA-256 43ebed18…, 324 sections, 0 problems; fresh
  Git-export rebuild verified 324 segments).
- environment: `preflight.log` (4 CPUs; cgroup v1, unlimited limit, MemAvailable 15.39 GiB;
  29.09 GiB free ext4) PASS; `toolchain-install.log` (Lean 4.25.0; Lean started normally, no
  `/proc` shim used); `cache-store.log` (store absent: 0 files); `cache-get.log` (239 roots,
  3,331 files downloaded, 0 failed, exit 0); `package-check.log` (11 present match, 4 ABSENT:
  doc-gen4, UnicodeBasic, BibtexQuery, MD4Lean; RESULT: PASS); `cache-check.log` (0 empty oleans);
  `cache-probe.log` (probe importing the first root; see its notes — two harmless setup
  attempts before the passing run).
- bootstrap at base: `bootstrap-base/summary.log` (51 modules, failed=0).
- cp01 module chain at the cp01 commit: `elab/cp01.summary` (Simulation through
  TimeConstructible, all exit 0, 0 errors; sorry warnings only in the not-yet-edited files).
- axioms: `axioms/Ax_cp01.*` — 11 names, all within {propext, Classical.choice, Quot.sound}.
- freeze: `freeze-cp01.log` — RESULT PASS (no public add/remove, no header/visibility/order/
  import/definition-body change in the 11 owned files).
- deviations: `deviations.log` (D1: a 3-second overlap of one leanelab elaboration with the
  bootstrap's Catalog compile; D2: a self-deadlocked wrapper, no Lean ran).

## NOT RUN at cp01
Seal/controls, unfiltered compiled census, copy-text screens (base and final), the 641-module
final sweep, campaign/policy lint. These follow at later checkpoints.

## Original evidence vs fresh runs
Everything above is a fresh run on this host except the packet's historical gate 16 evidence and
the maintainer's base screen, which are data only.
