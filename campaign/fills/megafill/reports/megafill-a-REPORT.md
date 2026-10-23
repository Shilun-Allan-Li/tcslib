# Megafill A — session report (Part 3, item 6)

Queue (cover brief `megafill-A.md`; addendum v2.4 Part 3), one session, one clone, branches from
the shared base `6cfee54474e3d954e3395f9d9eab5d025452a8dd` (ancestor check of the base into
`complexity/arora-barak-ch3-4`: PASS at session start). All five attachments' SHA-256 verified
against the cover brief's table at dispatch.

## Shared setup (once)

- Preflight 2026-10-22T05:11:11Z: disk 26.5 GB available (floor 12 GiB PASS); memory headroom
  = MemAvailable = 15.24 GiB (floor 4 GiB PASS; no cgroup limit); no oom events; 4 cpus.
- Toolchain `leanprover/lean4:v4.25.0` via elan.
- One narrowed cache fetch for the union of the three order lists' Mathlib roots: 41 roots,
  1023/1023 files, "Completed successfully!"; zero-size olean scan empty; root probe elaborated.
  `TAR_OPTIONS=--no-same-owner` set. No `lake build`; no unfiltered `lake exe cache get` ever ran.
- Disk re-checks before items 2 and 3 (Part 3 item 4): 21.8 GB before item 3 (10:58:05Z); 21.8 GB before item 2 —
  all above the 3 GiB floor.

## Item 1 — R cont2 (`Turing.exists_ndInterpreterCore`, `NDCodeSimulator.lean`)

- Branch `fill/c1-core-cont2`, created 2026-10-22T05:18:49Z; budget 4 h; ended 09:07:07Z
  (packaging; the final proof commit landed within budget).
- **Outcome: COMPLETE.** The target is proved modulo exactly the two cited stubs
  (`exists_replayCanonizer`, and `serialize_eq_tableBitsK`'s bridge is clean); the overlay's 20
  `ic_` privates kept verbatim; 5 new privates; the 12-phase startup assembly, the replay, the
  verdict cut and the ledger all closed. Checks: 80-module sweep exit 0; import probe exit 0;
  axioms `[propext, sorryAx, Classical.choice, Quot.sound]` for the target (sorryAx only via the
  cited stub); lint 0 FAIL; screens with 2 documented pairs (one 69% cross-file flagged).
  Disclosures in its REPORT.md: the seal test was run as inspection only; sweep-log process
  artifacts documented.
- Zip `fill-c1-core-cont2.zip`, SHA-256
  `4a2896a39cba455ef03997b8d5162c979569615f97f68a7087fe1feea159ce9b` (delivered 09:04Z; checkpoint
  cp4 delivered earlier).

## Item 2 — UN cont1 (`Turing.exists_timed_universal_NDTM`, `Diagonalization/NTimeHierarchy.lean`)

- Branch `fill/c1-universal-cont1`, created 2026-10-22T09:07:40Z; budget 3 h; delivered at
  10:58:31Z (1 h 51 m of the 3 h budget).
- **Outcome: COMPLETE.** The setup machine `P` built as an 8-phase seam chain (embedded header
  pass through `prefixCanonTM (pairExtractTM true false)` with the capture, buffer rewind+clear,
  a guided bank erase uniform in the extractor's unpublished tape count, the expansion, block
  rewind, counter clear, input rewind), `un_setup` proved with a clean axiom walk, and target 1
  closed by `exact un_universal_of_setup c un_setup`. `CP = 7|α| + 130`; target's
  `C = CP + CR + 13`. Checks: 75-module final sweep, confirmed 75/75 built, 0 errors, 25 sorry
  warnings (base's 26 minus the target's); import probe 95 checks 0 errors; seal test with 28 defs
  `local irreducible` (exit 0) and a failing control; axioms clean for every new private, the
  target's `sorryAx` only through the cited core stub; lint 0 FAIL; screens: no pair at 90%+,
  4 new pairs justified.
- Zip `fill-c1-universal-cont1.zip`, SHA-256
  `27ff57c319c2a7b6906ba3454de73b285878f00d996128aa49cbb0c33cdbdd69` (delivered 10:58Z; an
  earlier packaging of the same content, SHA `5312a4e2…`, was superseded minutes later so the
  bundle and patches carry the final style-wrap commit).

## Item 3 — B5a canon cont7 (`exists_canonGrammarStage`, `CodeSimulator.lean`)

- Branch `fill/b5a-canon-cont7`, created 2026-10-22T10:58:17Z; budget: the rest of the session.
- **Outcome: COMPLETE** (the stub proved at 17:53Z; delivered 20:53Z). Checkpoints 1–5:
  the record round instantiated on the generic counter-loop link; the inner block (write row +
  inner counter loop through the seam, adapter-wrapped); the table block (outer loop,
  consumption-bounded n-free ledger); the stage front (seven framed counter-preparation rows +
  the embedded bounded unary reader as one phase host); the assembly (a four-phase host — front,
  release-wrapped embedded table, native suffix test, park — folding `canonGrammar`'s three
  binds into the exit bit on every path). One disclosed amendment pass before checkpoint 5
  (unconditional empty-output clauses on this fill's own checkpoint lemmas 1–3) and one
  disclosed seal-hardening pass after it (definitional reads through `Cfg.select`/`Cfg.mapState`
  /`embedEmitCfg`/`FinTM.bufferTape` replaced by their published equations; proof-only).
  A third disclosed amendment restructured one lemma for duplication governance (the after
  screen found its induction skeleton echoing `Convention.lean::incFixed_length` across
  files; the rule admits no new cross-file pair — the final screen shows zero). Axioms: every
  new private, the proved stub, `exists_canonDecider` and the headline `exists_polyCanonizer`
  all within `[propext, Classical.choice, Quot.sound]` — no `sorryAx` in the headline. Final
  battery, all on the delivered tree: 118-module order list green (bootstrap 1–65 + sweep
  66–118 twice, 0 failures; sorry census = the base's 38 minus the stub); the five probes
  0 errors; the seal (35 foreign definitions locally irreducible) 0 errors with a failing
  control; note 50 elaborated, `note50_cases` axiom-clean; lint 0 FAIL at the base's exact
  WARN counts; screens before 2,419/2,633/824,240 (= base reference) and after
  2,455/2,692/885,426 with 59 new pairs, all in-file and justified, none ≥ 90% outside the
  deliberately parallel host legs, zero cross-file.
- Zip `fill-b5a-canon-cont7.zip`, SHA-256
  `7fd5aa40bcb49252a2d2f81e1fbf94e26bcc75b86a1bf9eba2d3ad54232c9e2c` (delivered 20:53Z;
  checkpoint zips cp1–cp5 delivered along the way).

## Queue discipline

- Items were worked strictly in order; no return to an earlier item after its zip.
- One Lean process at a time throughout (one deviation in item 1, disclosed in its REPORT: a
  briefly orphaned background sweep, killed; the authoritative sweep ran alone). One screen at a
  time, `nice -n 10` (one deviation in item 3, disclosed in its REPORT: the first before-screen
  launch looked dead and was replaced by a worktree-pinned run; the original turned out to be
  alive and was killed after ≈3 minutes of overlap; the survivor's log was opened fresh, so no
  interleaving reached it).
- Escalations: none on any item.
