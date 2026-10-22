# §13d G4 continuation 2 — E-RES environment report

**Outcome: E-RES, before the dependency cache and before any Lean invocation.**
No source changes and no completed fill checkpoint. Both target bodies remain `sorry`.
This is an environment report, not a checked partial fill or a failed proof attempt.

## Resource preflight

The initial preflight passed. The mandatory pre-cache recheck, after downloading and
extracting the pinned toolchain, found less than the required 12 GiB of free disk.
The run stopped under addendum v2.1 Part 1 and user instruction 1. No dependency tree
was copied, moved, reused, or deduplicated; no cache retry or attempt to make room followed.

| Measurement | Initial preflight | Pre-cache stop |
|---|---:|---:|
| UTC timestamp | 2026-10-18 15:36:22 | 2026-10-18 15:40:18 |
| `nproc` | 9 | 9 |
| Filesystem | overlay | overlay |
| Free disk, bytes | 16,582,742,016 | 12,038,127,616 |
| Free disk, GiB | 15.44388198852539 | 11.211380004882812 |
| `memory.max`, bytes | 8,589,934,592 | 8,589,934,592 |
| `memory.current`, bytes (informational) | 8,556,294,144 | 8,558,022,656 |
| `anon`, bytes | 1,009,508,352 | 1,258,123,264 |
| `kernel`, bytes | 369,500,160 | 494,206,976 |
| `shmem`, bytes | 0 | 0 |
| Headroom, bytes | 7,210,926,080 | 6,837,604,352 |
| Headroom, GiB | 6.7156982421875 | 6.368015289306641 |
| `oom` / `oom_kill` | 0 / 0 | 0 / 0 |

Calculations, using the prescribed memory-in-use definition:

```text
Initial:
  8,589,934,592 - (1,009,508,352 + 369,500,160 + 0)
  = 7,210,926,080 bytes > 4,294,967,296 bytes (4 GiB).
Pre-cache:
  8,589,934,592 - (1,258,123,264 + 494,206,976 + 0)
  = 6,837,604,352 bytes > 4,294,967,296 bytes (4 GiB).
Disk stop:
  12,038,127,616 bytes < 12 × 1,073,741,824
  = 12,884,901,888 bytes (12 GiB).
```

Page cache and `memory.events` high/max counters were not treated as shortages.
The full `memory.stat`, `memory.events`, `df -B1`, and `df -T` outputs are in
`evidence/logs/preflight.log` and `evidence/logs/pre-cache-resources.log`.
The pre-cache log covers the clone, workspace, runtime, temporary directory and log directory;
all are on the same disk-backed overlay. Its first `df` snapshot reports 12,038,389,760
available bytes; the subsequent threshold computation reports 12,038,127,616. Both fail.

## Input integrity and checkout

- Brief SHA-256 verified:
  `3584091a9a29046cc71871c73bb4cf2395678a1bfa6a47ca32f86b72cd062a87`.
- Addendum v2.1 SHA-256 verified:
  `2563c8d2ffed3e1fa268748edb017577522cec14a922ad2989d1aa974ab12d15`.
- One fresh clone of `https://github.com/Shilun-Allan-Li/tcslib`, initially on
  `complexity/arora-barak-ch3-4`, at tip
  `0bf4f0856baec53a519742a82e2d53ef30bfb839`.
- That tip's `campaign/fills/s13d/briefs/s13d-fill-g4-cont2.md` is byte-equal to the
  attachment after substituting the base hash for `@ANCESTOR@`.
- `git merge-base --is-ancestor 96d60278e4fde29b986ec1d0e59cd07f768fe28a HEAD` succeeded at the campaign tip.
- Created `fill/s13d-g4-cont2` at exactly `96d60278e4fde29b986ec1d0e59cd07f768fe28a`.
- No rebase, merge, cherry-pick, push, or PR.
- Base: `96d60278e4fde29b986ec1d0e59cd07f768fe28a`.
- Delivery marker: `f75cebef051d4cfc7f012cfe1e4e91531c488455`, a single **empty commit** whose parent is the base.
  Its tree equals the base tree. It records only the environment stop, so a valid bundle
  with the requested sole prerequisite and a format-patch series can be supplied.
  It represents no proof progress and need not be integrated.

The bundle's only prerequisite is the base. `git bundle verify` passed; see
`evidence/logs/bundle-verify.log`. The patch is an empty-commit format-patch (generated
with `--always`); replaying that marker, if desired, requires `git am --empty=keep`.
The full delivered source is byte-equal to the base source. The repository worktree is clean.

## Runtime and checks

Lean 4.25.0's Linux release archive was downloaded fresh from the official release and
extracted in this workspace using `tar --no-same-owner --zstd` (exit 0).
No other session's toolchain, cache, checkout or object store was used.

The pre-cache resource gate failed before `lean --version`. No Lean startup error was
observed; the Part 2 fallback condition therefore did not arise. No shim was created,
preloaded or shipped. No `LEAN_SYSROOT`, `LAKE_HOME`, `LD_PRELOAD`, `LEAN_PATH`,
`TCSLIB_OLEANS`, or `TMPDIR` override was used.

`lake exe cache get` was **not run**. Its required environment would have included
`TAR_OPTIONS=--no-same-owner`. No `.lake/packages` tree was created, so package-pin,
empty-olean and Mathlib-import checks were not reached. No `lake build` was run.
The bootstrap order was inspected: the owned file's prerequisite closure contains
22 modules including the owned file, within the prescribed 81-module order.
**Zero modules were elaborated.** All checks requiring those prerequisites were skipped.

| Required verification | Result |
|---|---|
| Bootstrap | Not run — E-RES before cache |
| Owned-file elaboration | Not run — prerequisites absent |
| Final 81-module sweep | Not run — prerequisites absent |
| Import probe, 338 names | Not run — prerequisites absent |
| Axiom prints and admission walks | Not run — prerequisites absent |
| Seal test | Not run — prerequisites absent |
| Rewrite/unfold argument inspection | Empty source diff; no new arguments |
| Six forbidden R3 rows in diff | Empty source diff; no hits |
| Style lint | Not run after E-RES |
| Import/statement/ownership changes | None; whole repository tree equals base |

The bootstrap, final-sweep and axiom-log files explicitly say **NOT RUN**.
There is no final-sweep tail or current axiom result to claim.

## Checkpoints and open work

**No checkpoint completed; no `cp<N>` ZIP written.** The final filename is
`fill-s13d-g4-cont2.zip`, containing this environment report and the available evidence.

| Item | Status |
|---|---|
| Phase 0 inherited kit | Unchanged; not rechecked here |
| Restate/remove `zr_left_two_walks` | Not attempted before E-RES |
| Phase 1 checkpoint 1: right pass | Not started |
| Phase 1 checkpoint 2: return home | Not started |
| Phase 1 checkpoint 3: amended left pass | Not started |
| Phase 1 checkpoint 4: level-zero branch | Not started |
| Phase 1 checkpoint 5: cleanup | Not started |
| Phase 1 checkpoint 6: assembly | Not started |
| Phase 2 scan, guarded move, passes, mirror, cleanup | Not started |

Open declarations:

- `Turing.exists_zoneExtendTM` — original `sorry` body unchanged.
  **Proof sketch.** Compose the prescribed right pass, return home, amended left pass,
  level-zero finite-control branch and scratch cleanup; assemble the segments with
  `Contract.ofSegment` and the required head envelopes. Use the amendment's extra
  leftward cell and charge every dispatch and ruler restoration.
- `Turing.exists_zoneRebalanceTM` — original `sorry` body unchanged.
  **Proof sketch.** Compose the two-exit feeding-side scan with `Round.iterate`, the
  guarded column moves and four side passes around the home move; use the mirror for
  the other direction, clear scratch and assemble the prescribed contract and bounds.

Neither target's axiom walk was run. The inherited bodies remain the original
admissions; this delivery introduces no additional declaration or admission.

No private declaration was added, changed or removed. No leaf, host, tape or import was
added. Both public-facing status paragraphs remain byte-for-byte inherited because
work stopped before any edit. Their required rewrite remains continuation work.

No left-pass option was implemented or selected. The brief's level-one calculation
was checked arithmetically only, not in Lean: `zoneStart 1 = 5`, old seek stop `2-5=-3`,
required displacement `2·2^1+1=5`, and new outer end `-3-5=-8`. Either prescribed
amendment covers those five cells. No scratch layout or adjusted walk was implemented.

Promotion candidates: none newly implemented. The inherited one-cell leaf, bridges and
mirror remain candidates, with their existing contracts unchanged. The only escalation
in this run is **E-RES (disk)**; no mathematical obstruction is claimed.

## Duplication and source inventory

The baseline v3 screen was launched once under `nice -n 10`, before edits, on the
prescribed ten-file population. After E-RES it was interrupted through its running
execution session (exit 130). It produced no completed output; its partial stdout and
stderr are empty and retained. No second screen was run. `screen-after.txt` explicitly
records the skipped check. The repository's baseline figures (808 declarations,
439 pairs, 127,994 characters) are maintainer measurements, not measurements reproduced
by this run.

**new copies: none** — there is no source diff. There are no new in-file or cross-file
pairs to justify; this follows from byte identity, not a completed screen.
No declaration outside the file was cited by a new proof because no proof was added.
There are no new `rw`/`simp`/`simpa`/`unfold` arguments or forbidden R3 references.
No new seal list was constructed.

Final owned-source size: **861 lines, 18 public declarations, 31 private declarations**,
unchanged from base. No new long lines or changes outside owned regions exist.

The base sorry-warning inventory was recorded before any fill (not reproduced by Lean):

```text
TuringMachine/Simulation: 1: branchTM_spaceUsed
TuringMachine/Encoding: 1: pairDiagTM_computes
ClassP/TimeConstructible: 2: _root_.Turing.FinTM.lengthBitsTM_computes, _root_.Turing.FinTM.lengthBitsTM_spaceUsed
TuringMachine/Composition: 3: idTM_computes, ifEqTM_computes, condTM_computes_iff
TuringMachine/Build/Wrappers: 2: timedCondTM_computes, timedCondTM_spaceUsed
TuringMachine/Build/Loop: 5: loopHostTM_contracts, loopHostTM_decides, loopHostTM_finds, loopHostTM_spaceUsed_le_budget, emitLoopTM_computes
TuringMachine/Build/Primitives: 3: polyUnaryTM_spaceUsed, unaryTokenTM_computes, appendBitTM_computes
TuringMachine/Build/InputDevice: 3: exists_rulerTestTM, exists_rulerDeviceTM, exists_rulerHostTM
TuringMachine/Build/InputWindow: 1: exists_inputWindowCopyTM
TuringMachine/Build/RecordTable: 4: exists_tableFindTM, exists_tableAppendTM, exists_recordValidTM, exists_recordNextTM
TuringMachine/Build/SeamLayout: 1: exists_seamLayoutTM
TuringMachine/Build/ZoneRebalance: 2: exists_zoneRebalanceTM, exists_zoneExtendTM
TuringMachine/CodeSimulator: 2: exists_canonGrammarStage [private], exists_uniformSimulator
TuringMachine/NDCodeSimulator: 2: exists_replayCanonizer, exists_ndInterpreterCore
TuringMachine/UniversalK: 3: exists_selfStartupTMK, exists_selfUniversalK, universalK
TOTAL 35
```

## REPORT.md checklist

- [x] Preflight numbers recorded under v2.1, using `anon + kernel + shmem`.
- [x] Base and ancestor check recorded; no completed checkpoint or checkpoint ZIP.
- [x] Declaration changes listed: none. Helper amendment and status rewrite not reached.
- [x] Left-pass status and level-one arithmetic recorded; no implementation claimed.
- [x] Scratch layout/walk status recorded: not implemented.
- [x] Promotion status and E-RES escalation recorded.
- [ ] Rule 10 probe and seal test: blocked by E-RES; empty-diff inspections recorded.
- [ ] Both v3 screens completed: baseline interrupted; after skipped. Raw status retained.
- [ ] Final sweep, axiom prints and lint: blocked by E-RES. Source counts and freeze recorded.

Resume on a host with at least 12 GiB free **after** provision of the pinned toolchain,
with at least 4 GiB of memory headroom computed as above. The completed work to retain
is input/checkout verification and this environment evidence; no proof checkpoint exists.
