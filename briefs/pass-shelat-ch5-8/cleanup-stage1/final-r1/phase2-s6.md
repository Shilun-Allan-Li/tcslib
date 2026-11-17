# cleanup-stage1 · phase 2 re-replay on olean snapshot #6 (merge condition for #347 + #355)

**Verdict: PASS.** The prospective tree TS2 = records tip × #347 × #355 builds cleanly on olean snapshot #6 (T `8060f6b7`,
the #357 merge). All 561 downstream modules rebuilt with rc 0 and 0 errors. The checks at TS2 equal phase 2's records at
TS1 `1eaf940b`; every difference comes from #357:
- **admissions:** 192 at the tip and 192 at TS2, identical module by module;
- **axioms:** standard only. The probe log is byte-equal to phase 2's;
- **coe-A seals:** on the 21 owners, request sets, rc, errors and probe logs are byte-equal to phase 2's. The record
  JSON differs only in `rev`;
- **lint:** unchanged.

`$SP/olean-replay-cs1-s6` is the snapshot candidate. It is adoptable at a merge whose Lean equals TS2's tree (§5).

- Date: 2026-11-17 UTC, 16:14–17:40. `$SP` is the maintainer scratchpad, as in `maintainer/snapshots.md`.
- **Lean processes:** one at a time. Before each one, a gate counted host-wide `lean` processes and waited (30 s polls)
  while there were 3 or more.
  - The gate saw at most 2 at every start (562 build gates, 23 probe gates), so it never had to wait.
  - The 30-s watchers saw at most 3 host-wide, including ours.
- **Disk:** the same gate refused to start a module below 1500 MB free. It fired once (§2, attempt 1).
- No `lake build`, no cache get. Nothing was committed or pushed, and no PR or other record was edited.
- Evidence: `cleanup-stage1-final-r1-phase2-s6-evidence.zip` under `cs1-final-r1-phase2-s6/`, with its own
  `SHA256SUMS` listing the other 696 files. Its SHA-256 is in `evidence-SHA256SUMS`.

## Inputs
| What | Value |
|---|---|
| Records tip (fetched by name) | `6f13855029e918d4a0c19d17efbc35eedbb902f8`. 0 Lean, toolchain, manifest or lakefile paths differ from `8060f6b7`. At the end of the job the tip was `3c14bfc42691cb2344351bda9ce86172b829089c` (records only: 0 such paths against `6f138550`; tip × #355 has the same Lean as TS2) |
| Snapshot #6 | `$SP/olean-snapshot`. Map `olean-snapshot.map-8060f6b7.tsv`, SHA-256 `0858dccbee016da1da450f2b2ca0d1f5094ee42646b9496d5278f2b45cb07caf`; files manifest `1ae04ef5f80e99b331d5062546831c9a180354a88181d4233d5eacf57433c86e`. Both equal the copies in `maintainer/olean-snapshot-6-adopt/`. 1463 entries |
| #347 | `daa6e173cdd94cad1475b9a96eca613bce53ba61`. Remote head unchanged at start and end |
| #355 | `d3c7cb00092ad5913904654d922f30fc7d5fce4a`, tree `508f915413ee8ef9f2a37b59e0012c9daf3867aa`. #347 is its ancestor. Remote head unchanged |
| Recipe | `phase2.md` and `$SP/cs1p2/` (its scripts, reference lists and records, read only). Snapshot procedure: `maintainer/snapshots.md` and `olean-snapshot-procedure.md` |
| Recipe tools | `$SP/snaptools3/olean-advance-a6d01b1b/tools-used/`, read only. 63/63 hashes equal phase 2's list (`tools/recipe-tools-vs-phase2.txt`) |

## 1. Prospective tree TS2
- **Merge orders.** `git merge-tree --write-tree` was clean in all five of phase 2's orders:
  - (tip × #347) × #355;
  - tip × #355;
  - #355 × tip;
  - #355 × (#347 × tip);
  - (tip × #355) × #347.

  Every order gives **TS2 = `13fc8060d5b8d08a8f9e80244242118acaa679e2`**. tip × #347 is `6511c24c…`. The three
  intermediate trees were passed as unreferenced temporary commit objects (`git commit-tree`, no ref).
- **Against the Gate 47 pack.** Gate 47 computed pin × #355 as `1a1548572d49879ee262d704da431180aefb3a39` (first pin) and
  `20d1101ade46ba26919f01e30f7ee9422495669b` (pin `659542ec`).
  - TS2 differs from both only in records: 42 and 18 non-Lean paths, and **0 Lean, toolchain, manifest or lakefile
    paths**.
  - The `TCSlib` subtree is `4b4583151bd9f704dc9fe80731ebb0d9bf2b725e` in all three trees. `audits`, `TCSlib.lean`, the
    toolchain, the manifest and the lakefile are equal too.
- **TS2 against the tip.** Exactly 23 paths change, all Lean, +1,332/−296: #347's and #355's 23 files.
  - The path set equals TS1's against phase 2's tip `e1d39836`.
  - The Lean diff tip → TS2 is **byte-equal** to phase 2's diff `e1d39836` → TS1.
  - Each of the 23 TS2 blobs equals TS1's. Each equals #355's except `Games.lean`, the union file already described in
    phase 2.
- **TS2 against TS1.** The Lean difference is exactly #357's 9 files, each blob-equal to T `8060f6b7`:
  - `Games/Relational`;
  - `IdentityBased/{Defs, BonehBoyen, BonehBoyenSecurity}`;
  - the 5 new `BonehBoyenSecurity/{Chain, Coupling, Lazy, Random, Real}`.

  So **TS2's Lean = TS1's 23 PR files on top of `8060f6b7`'s Lean** (`merge/mergetrees.txt`).
- **Export.** The tree was exported from TS2 with `git archive`: `TCSlib`, `TCSlib.lean`, `audits`, `scripts`, the
  toolchain, the manifest and the lakefile. `.lake/packages` is a symlink to the repository's.
  - 1468 `.lean` files (T's 1466 plus `Games/Tapes` and `ZeroKnowledge/InteractionWords`). The path set equals the tree,
    and every file was blob-verified.
  - The export was deleted after the probes; it can be regenerated from TS2.

## 2. Replay (recipe steps 1–5)
- **Copy and overlay.**
  - `cp -al $SP/olean-snapshot $SP/olean-replay-cs1-s6`.
  - `mloverlay.sh` gave 3346 symlinks.
  - `mathlibextra.sh` (slot-gated) compiled NthRootLemmas to olean
    `c0a9cff04c6707edac6980cf4d3c3cc8116ab8843e9ddfb82f6688aee8e0f54c`.
- **Plan.**
  - `stateplan init` at T over the #6 files manifest keyed 1432 modules.
  - `downorder`: changed 23, down 561, order 1434.
  - `fullorder`: roots `TCSlib` and both `audits/*/Checks`, **full order 1434**.
  - `stateplan plan`: **build 561**, reuse 873. The queue is exactly `down`.
- **The 561 against phase 2's 556:** the 556 plus #357's 5 new `BonehBoyenSecurity/*` modules. Nothing is missing
  (`plan/queue-vs-phase2-556.txt`).
- **Build:** recipe `runner.py` with one change, the pre-module slot/disk gate (`tools/scripts/runner_gated.py`; the diff
  is the gate block only). `TCSLIB_OLEANS=$SP/olean-replay-cs1-s6`.
  - **Attempt 1,** 16:33:38–16:44:54: 114 modules, all rc 0.
    - Before the 115th module (`Asymptotic/HardCoreCollection`), the gate read 1277 MB free and stopped the runner
      (`stopped_at` record). No Lean process of ours was running.
    - The drop came from outside this job. Free disk fell from about 2.4 GB to 441 MB within about two minutes while this job's
      new files came to about 0.1 GB. It was back at 2.3 GB a minute later (`build/disk-dip.log`,
      `watch.log.attempt1`).
  - **Resume,** 16:48:27–17:21:25, from `HardCoreCollection`, after two minutes of steady readings around 2.25 GB
    (`run-build-resume.sh`). 447 modules.
    - That module's olean was still the snapshot's hard link when the run resumed, so nothing half-written was reused.
    - The results file holds one record per module: 561 records, 561 distinct, in queue order.
  - Module time was 2649 s; the longest was CookLevin/Hardness at 237 s. Max RSS was 4.35 GB.
  - **561/561 rc 0.** `error:` 0, `error(` 0, the substring "error" 0. 22 sorry warnings (TQBF 21, NonUniform 1), 268
    warnings. `permod`: 0 log/record mismatches.
  - Phase 2 had 26 sorry warnings and 272 warnings. The −4/−4 are #357's: `Games/Relational` and
    `BonehBoyenSecurity` went 2 → 0 each.
- **Accept:**
  - `stateplan update`: 561 modules, none refused.
  - `check` over the 1434: **1434/1434 OK, RESULT OK**. This was re-run after the probes, with the same result.
  - **Link count 1 on all 561 rebuilt oleans,** after the build and again after the probes.
  - The 873 reused oleans are the snapshot's inodes.
  - No `.ilean`, and no symlink outside `Mathlib/`. `Mathlib/` holds 3346 symlinks and the NthRootLemmas olean.
- **Snapshot #6: `snapmap verify` gives 0/0/0, RESULT OK,** at three points:
  - before the copy;
  - after the build;
  - after every probe (end).
- **Cross-check against phase 2's build (determinism).**
  - 542 of the 561 modules have the same closure key at TS2 as at TS1. All 542 have **byte-equal oleans and byte-equal
    logs** to phase 2's.
  - The 14 whose key #357 changed and the 5 new ones are listed in `build/objects-vs-phase2.txt`. Only 4 of the 14
    objects differ.
- **Output map** (LE-g48's `mapnoml.py`, i.e. the map that recipe step 6's `snapmap.py make` would give once `Mathlib/`
  is removed):
  - `output-map/olean-replay-cs1-s6.map-13fc8060.noMathlib.tsv`, **SHA-256
    `5105c5149901c5c4375083c1f6ad998b70c909905e4fbf430c9e96117a0f7300`**;
  - 1465 entries: TCSlib 1432, audits 2, PFR 31. A recheck gives the same hash;
  - against snapshot #6's map: 1440 equal, 23 changed (21 of the PR files' modules plus `Randomized/Repetition` and
    `SeedMajority/Enumeration`), 2 added (`Tapes`, `InteractionWords`), 0 removed.
- **Replay directory state:** `$SP/olean-replay-cs1-s6` (1.4 GB apparent, mostly hard links). The checked state is
  `plan/state-after-update-13fc8060.json.gz`.

## 3. Checks at TS2
### Admissions
- `tipcensus.py` used LE-g48's record sets (the same 17) plus this replay's records.
- **At the tip `6f138550`: 192**, over 1432 modules with a record. The per-module table equals LE-g48's census at #357's
  head `dfdc56f2`.
- **At TS2: 192, identical module by module.** The only rows that differ are the two new modules, absent → 0. The 561
  rebuilt modules carry 22 sorry warnings at both revisions.
- **196 − 4 = 192 confirmed.** Phase 2's T census (196, `e1d39836`) against the current tip differs only in #357's modules:
  - `Games/Relational` 2 → 0;
  - `BonehBoyenSecurity` 2 → 0;
  - its 5 new modules, absent → 0.

  TS2 against phase 2's TS1 census shows the same 7 rows, 196 → 192.
- Source scan: the tip → TS2 Lean diff adds and removes 0 `sorry`, `admit` or `native_decide` tokens.

### Axioms (`axioms/`; one probe on the replay)
- The probe is phase 2's: same generator, name lists and import lists. `Axioms.lean` is byte-equal to phase 2's.
- The log is **byte-equal to phase 2's**: rc 0, 78.7 s.
- **Stage 1's 69:** all within {`propext`, `Classical.choice`, `Quot.sound`}. The split is 34/12/6/4/13.
- **#347's 27:** all exactly the standard three.
- **Census of every constant in the 21 owners:** 1224 constants, all standard. No `sorryAx`, and 0 errors.
- The 80 touched declarations (tip → TS2: 57 added, 2 changed, 21 new-file) are all in the census. `touched.tsv` is
  byte-equal to phase 2's.

### Canonical coe-A seals, 21 owners (`rule10/`; driver `tools/scripts/rule10_cs1s6.sh`)
- **Method:** phase 2's head driver, narrowed to the collector, `mkseals_coe.py` variant A and the axioms probe.
  - It uses the same archived Gate 06/10 instrumenter and the same owner list.
  - It keeps phase 2's probe prefix `CS1P2H` and collector title, so the probe sources compare byte for byte.
  - The collector source and log are byte-equal to phase 2's.
- **Against phase 2's records** (`cmp/seals-coe-A-vs-phase2.txt`):
  - phase 2's `sealcmp.py`: **21 compared, 21 same, 0 diff**;
  - per record:
    - the request sets (`rows[].spelling`) are set-equal;
    - `requested`, `term_names`, `term_in_closure`, `stored_constants` and `closure_modules` are equal;
    - `source_sha256` and `probe_sha256` are equal;
    - rc, the error lines and the whole probe log are byte-equal: **21/21**;
  - the record JSON differs from phase 2's **only in `rev`** (TS1 `1eaf940b` → TS2 `13fc8060`), in all 21 records and
    the manifest.
- **Failures, all pre-existing and as recorded in phase 2:**

  | Owner | Errors | Failing declarations | Item |
  |---|---|---|---|
  | `IterateFindHost` | 16 | `copy_*`, `host_dispatch`/`branch`/`halt` | DW-9 |
  | `ModuleHost` | 10 | `stop_*`, `clean_*`, `pad_*`, `host_seam`, `host_call` | DW-9 |
  | `Trapdoor` | 3 | `acceptProb_owpGen*_unit`, `predProb_pkPredictor_eq` | pre-existing |
  | `Entropy` | 5 | `IsFlatSource.isSource`, `isSource_uniform`, `le_minEntropy_iff` | DW-10, CS1-F07 |

  The other 17 owners: rc 0, 0 errors. None of the 80 touched declarations fails. Every probe had its install and EOF
  records.
- **Differences to explain: none.** #357's files are not owners, and all 21 owners have the same closure key at TS2 as
  at TS1, so no owner imports them.
- **Not re-run, as this job did not ask for them:** strict, B and coe-B seals, the paired controls and the
  explicit-unfold scan.
  - The inputs these depend on are unchanged from phase 2: the owner sources, the collector output and the coe-A probes
    are byte-equal, and the owners' oleans are byte-equal as well.

### Lint (`lint/`; same scripts at the tip and TS2)
- **`campaign_style_lint --check8b`,** FAIL/WARN line multisets with line numbers dropped:
  - Cryptography 92/104 → 92/103: the only change is the removed `Trapdoor` `pkPredictor` WARN;
  - InformationTheory 5/2 → 5/2;
  - Complexity 25/390 → 25/390.

  The tip → TS2 delta equals phase 2's tip → TS1 delta exactly. The current tip equals phase 2's tip and TS2 equals
  phase 2's TS1 in all three areas, so #357 changed no lint line.
- **`style_lint` on the 23 files:** byte-equal output to phase 2's, at the tip (21 files) and at TS2 (23 files). Both
  findings are pre-existing: the `BitLists` `## References` placeholder and `Strings` `canonFun_poly`, line 425.

## 4. Disclosures
1. **The disk gate stopped attempt 1 once.** An outside drop took free disk to 441 MB, and our runner was gated at
   1277 MB before the next module. I resumed after free disk was back and steady around 2.25 GB. The low point was not
   this job's doing. Free disk at the end was about 1.6 GB.
2. **The runners carry an added gate.** `runner_gated.py` and `runner_full_gated.py` are the recipe's `runner.py` and
   `runner_full.py` plus a pre-module slot/disk gate. That was required by this job's slot rule; the record format is
   unchanged.
3. **Checks narrowed to this job's list:** coe-A seals only. Strict/B/coe-B seals, controls and the scan were not re-run
   (§3).
4. **Housekeeping:**
   - `$SP/olean-replay-cs1` (TS1 on #5) was deleted at the start, after confirming that no process used it.
   - `$SP/cs1p2` was kept whole: its raw seal and scan logs are only hash-listed in the phase-2 zip.
   - This job's TS2 and tip exports were deleted after use. Its full seal records stay in `$SP/cs1s6/r10/`.
   - Three temporary unreferenced commit objects were created for merge-tree inputs.

## 5. Adoption (recipe step 6)
`$SP/olean-replay-cs1-s6` is the snapshot candidate **only at a merge commit whose Lean equals TS2 `13fc8060`**:
`git diff --name-only <merge> 13fc8060d5b8d08a8f9e80244242118acaa679e2 -- '*.lean' lean-toolchain lake-manifest.json lakefile.lean`
must be empty. That holds when #347 and #355 have both merged onto a tip whose Lean is still `8060f6b7`'s.
- If #347 merges alone first, adopt only at #355's merge, after the diff is empty.
- If any other Lean change (for example GSW 6a) lands first, discard this replay and replay again.
- At adoption:
  - remove `Mathlib/`;
  - make the map, which must have SHA-256 `5105c514…`, and the files manifest;
  - run `basecheck` against `plan/state-after-update-13fc8060`;
  - swap, verify 0/0/0, and add the `snapshots.md` row.

**Not yet clear to merge — Gate 47 must clear; this re-replay merge condition is met at TS2 `13fc8060`.**
