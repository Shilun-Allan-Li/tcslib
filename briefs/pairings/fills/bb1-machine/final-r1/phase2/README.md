# bb1-machine r1 · phase 2 (Lean) of the maintainer review of #346

**Result: every phase-2 check passes.** The final replay was run on snapshot #4. In it, #346 (T4 `exists_bb1_distinguisher`, with LE-bb1m) builds with rc 0 and 0 errors. The rest:
- the state check over the full closure is OK;
- T4 is standard and `bb1_sidSecure` reaches exactly T2 and T3;
- admissions go down by 1, exactly T4;
- all 32 canonical seals have 0 errors, with request sets identical to the worker's;
- the paired controls, including the new `Oracles`-owned probe (BM-F03), are ALL_OK in both variants;
- the scan finds 0 foreign items, and lint has nothing new.

The cross-build with #340 is clean: admissions go down by 2, T1 is standard, and the #340 seals have 0 errors. The final verdict is **ACCEPT WITH LANDING EDITS**: LE-bb1m is already in #346 and builds. The review is clear for Gate 44.

The job ran on 2026-11-17 UTC, 00:20–03:45. `$SP` is `/tmp/claude-0/-home-user-tcslib/d0667d12-db8d-5853-b0f7-9833dc0884c6/scratchpad`. All records are in `phase2-evidence.zip`, under `bb1-machine-r1-phase2/`; `PROVENANCE.txt` there gives the layout. Nothing was committed or pushed.

## Inputs and prospective trees

The records tip moved during the job, and the coordinator advanced the olean snapshot twice: #351 merged, then #352. The verdict rests on the last replay, **346c**. The two earlier replays are supporting evidence.

| Replay | Snapshot (T, map) | Records tip | tip × #346, both orders | tip × #346 × #340, all orders |
|---|---|---|---|---|
| 346 | #2 `a6d01b1b`, `95493449…c111` | `ff0c2552` (later `7486e401`, Lean-equal) | `278c549ceca1a61c79958720e545d7637e790912` (`7486e401`: `ac9e7958…`, Lean-equal) | `b90b966bc40a20e3f806cdc2379178c201b1b262` (`7486e401`: `786ea8ae…`) — **built** |
| 346b | #3 `cf7d28f7` (#351), `e9dfbfdd…a53d` | `c0752b2e` | `2acfdbcdf80f0ce59dca78ba198af89d8e8501b1` | `33a9c30b…` (not built) |
| **346c** | **#4 `463f2244` (#352), `6607620d725049c90b34a51a2ab891f1520fd0f576aaf3f9d51301222cee41e7`** | **`ca129d64cd54a92aabe517e5262058664b49f651`** | **`2ec7251551dfb6ee84ff8c11c15e0544a0d16b79`** | `c7be1301f59ec0f208f2645544abac8ac5cc6626` (not built) |

- **Tips.** Each records tip is Lean-equal to its snapshot's T: `git diff` over `TCSlib`, `TCSlib.lean`, `audits`, `scripts`, the lake files and `lean-toolchain` is empty.
- **Merge orders.** Every merge is clean, and every order gives the same tree. For the three-way merge I tried (tip × #346) × #340, (tip × #340) × #346 and (tip × #346) × (tip × #340).
- **What the merge changes.** Against its tip, each tip × #346 tree differs in exactly the 8 owner files. Each of those files is blob-equal to the PR head.
- **Heads.** `refs/pull/346/head` is `89a18a82` and `refs/pull/340/head` is `916afc25`, at the start and at the end of the job.
- **#346 commits.** It has 7 commits, all with `gpgsig`.
- **Range-diff.** `git range-diff 9e7a9648..c90273fa 7291f6b2..0da95f96` shows 6/6 identical, and the six picks reproduce the worker's 8 blobs.
- **LE-bb1m.** The 7th commit is `Oracles.lean` only, +2/−8, and its body is identical to `landing/LE-bb1m-proposed.diff`.
- **`IdentityBased` facade.** It is unchanged.

## Replay 346c on snapshot #4 (final; `final-346c-snapshot4/`)

- **Copy.** I ran `cp -al $SP/olean-snapshot $SP/olean-replay-346c`, which gave 1453 files, all hard links. Before the copy, snapshot #4 rehashed 0/0/0 against its map.
- **Mathlib.** I added the overlay of 3346 symlinks and built NthRootLemmas into the output only. Its olean is `c0a9cff0…`.
- **Order.**
  - `downorder.py` against `463f2244` gives changed 8 and down 12.
  - `fullorder.py` gives the full closure of 1427 modules: root `TCSlib` and both `audits/*/Checks`.
  - `closurecheck.py` finds 0 missing and 0 extra.
- **Plan.** `stateplan.py init` at `463f2244` over `olean-snapshot.files-463f2244.txt` keys 1422 modules. The plan has **12 to build** and 1415 to reuse, and the queue equals the downstream set. The 12 are:
  - `Defs` and `BonehBoyen`;
  - the five helpers;
  - `BonehBoyenMachine` and `BonehBoyenSecurity`;
  - the `IdentityBased` and `AdvancedEncryption` facades;
  - root `TCSlib`.
- **Build.** `runner.py` ran each module through `scripts/lean_check_tree.sh`, one Lean process at a time, from 03:28:39 to 03:29:42.
  - **12/12 had rc 0, with 0 `error:`, 0 `error(` and 0 occurrences of the substring "error".**
  - The 8 owners have **0 warnings**. `BonehBoyenSecurity` has exactly **2 `sorry` warnings**, at `:89` and `:104` (T2 and T3).
  - All 12 oleans are byte-identical to the snapshot-#2 build of the same sources.
- **State.** `stateplan update` took 12 modules. `stateplan check` over the 1427-module full closure gives **RESULT OK**. The keys of both `audits/*/Checks` are unchanged; they are reused from `463f2244`.
- **No write-through.** All 12 rebuilt oleans have **link count 1**, and the output has no `.ilean`. Snapshot #4 rehashed **0/0/0** against `olean-snapshot.map-463f2244.tsv` after the replay and again at the end (03:42 UTC).
- **Output.** `$SP/olean-replay-346c` is **kept**. It is the adoption candidate if #346 merges unchanged.
  - Its map, written in `snapmap.py` format with the `Mathlib/` overlay excluded, is `output-map/olean-replay-346c.map-2ec72515.noMathlib.tsv`. It has 1458 entries and **SHA-256 `5e63b3cc1a0efd40c3b5875d701b99a7457cc5f2a3b2831d4a7ab8cc7cf35404`**. This is the map that `snapmap.py make` will produce once recipe step 6 removes `Mathlib/`.
  - The map that also includes the NthRootLemmas build is `b672237a…`; the 3346 symlinks are skipped in both.
  - Compared with snapshot #4: 1450 entries are identical, 3 changed (`Defs`, `BonehBoyen`, `BonehBoyenMachine`) and 5 were added (the helpers). Four rebuilt modules came out byte-identical.
  - The prospective tree is `2ec7251551dfb6ee84ff8c11c15e0544a0d16b79`.
- **Axioms** (`probe-src/Axioms346.lean`: the worker's final probe, with T1 added to the trace) gave rc 0 and 0 errors. Its log is byte-identical to the snapshot-#2 run.
  - `exists_bb1_distinguisher`, `abs_expect_bb1Sim_sub_distinguisherL_le`, the 4 `BonehBoyen` readers and the three `BB1Machine` helpers: `[propext, Classical.choice, Quot.sound]`.
  - `IBEScheme.oracleImpl_{zero,one,two}_onSpec`: `[propext, Quot.sound]`.
  - Census of the 8 owners: **571 constants, 0 non-standard**.
  - Trace: T4 has closure 19638 and reaches **0** sorried constants. `bb1_sidSecure` reaches **exactly `bb1_sim_real` and `bb1_sim_random`**. T1 still reaches itself, because #340 is not in this tree.
  - All of these equal the worker's figures.
- **Admissions** (`tipcensus.py`; the build records of every snapshot generation plus this job's):
  - tip `ca129d64`: **198**;
  - tip × #346: **197**.

  The **change is −1, exactly `BonehBoyenMachine`** (T4). The 5 new helpers have 0. Neither census has a disagreement, and the same 34 modules outside root `TCSlib`'s closure have no record. Over the issued closure (that of `BonehBoyenSecurity`, 164 modules) the count goes **22 → 21**: the 18 Complexity admissions plus T1, T2 and T3.
- **Seals: relevance, and which seals I re-ran.**
  - Since snapshot #2, each owner's closure changed in exactly `Games/Probability` (#351, one theorem) and, for all owners except `Defs`, `Pairing/Group` (#352, three theorems). Neither change adds an attribute or a definition.
  - I regenerated all 32 seal records from a new collector run at `2ec72515`. The collector's `CAT`/`ROOT`/`CLOSURE`/`MODULE` records are **identical** to the snapshot-#2 run (0 diff lines). **All 32 request lists are identical**, row by row (name, home, instance, matcher, abbrev, reducibility), and **all 32 probe sources are byte-identical**. The owners' oleans are byte-identical too.
  - So no owner's request set can change, and no seal needs rerunning on this ground.
  - As a confirmation I ran the **canonical coe A** seal of all 8 owners on 346c. The 8/8 seals have rc 0, 0 `error:`, 0 `error(`, install and EOF records, no failing declaration, and requests 804/839/1644/2240/2273/2307/2308/2309.
- **Scan, run again here.** It covers 947 items and finds **0 foreign**. Its output is identical to the snapshot-#2 run. There are 5 fewer items than the worker's 952, because LE-bb1m removed the `have hpp` lines.
- **Lint.**
  - `campaign_style_lint.py TCSlib/Cryptography --check8b`, tip against tip × #346: 92 FAIL / 104 WARN on both sides, and the non-INFO line sets are identical, so there is **no new FAIL or WARN**.
  - The new INFO lines are only the helpers' lines and the size lines for `BonehBoyen` (714), `Handler` (899) and `Words` (632).
  - `style_lint.py` on the 8 files gives **0 findings**.
  - `sk15` finds only `BonehBoyen.lean:631 bb1SimChal_fresh` (BM-F06, pre-existing).
  - Widths are ≤ 100 in all 8 files, and `Oracles` has 367 lines.

## Snapshot #2: the full Rule 10 run and the #340 cross-build (`supporting-346-snapshot2/`)

**Replay of tip × #346** (`278c549c`, `$SP/olean-replay-346`):
- 12/12 rc 0, 0/0 errors, 0 substring.
- The state check over the 1426-module full closure is OK, and the link count is 1 for all 12.
- Snapshot #2 rehashed 0/0/0 before the build, after the build, after the container restart (01:36) and after the X build (02:50 UTC). The 02:50 check was my last before the #351 merge, at 03:00 UTC. Following the coordinator, I did not rehash #2 after it was retired.
- After the container restart I rechecked the output with the state check, the 12 link counts and a full rehash against the snapshot map plus the 5 new oleans: 1457 non-Mathlib oleans, 0 extra, 0 missing and 0 changed. It was complete. I re-ran every interrupted Lean phase from scratch (see Anomalies).

**Seals** (collector, then `rule10_b.sh` unmodified, `lean -DmaxErrors=0`, both error forms counted from the raw logs):

| Owner | strict A | strict B | coe A | coe B |
|---|---|---|---|---|
| `Defs` | 805 | 806 | 804 | 805 |
| `BonehBoyen` | 840 | 841 | 839 | 840 |
| `Draws` | 1645 | 1646 | 1644 | 1645 |
| `Words` | 2241 | 2242 | 2240 | 2241 |
| `Handler` | 2274 | 2275 | 2273 | 2274 |
| `Reduction` | 2308 | 2309 | 2307 | 2308 |
| `Oracles` | 2309 | 2310 | 2308 | 2309 |
| `BonehBoyenMachine` | 2310 | 2311 | 2309 | 2310 |

- **32/32: rc 0, 0 `error:`, 0 `error(`**, install and EOF records present, no failing declaration. The canonical coe A seals have 0 failing declarations.
- The counts equal the worker's table. All **32 request sets are identical**, name for name, to the worker's delivered records. `Oracles`' source differs only by LE-bb1m, which removes a `have`; it does not change a request.

**Paired controls**, with the worker's `mkctl_bb1m_readers.py` used verbatim:
- There are 24 probes per variant. In strict and in coe, the 314 sealed negatives each fail exactly once: 628 `error:` lines and 0 `error(` in all.
- Every positive passes, the 24 unsealed probes have 0 errors, and there are 0 stray errors. **ALL_OK True in both variants.**

**BM-F03: `Oracles`-owned control probes** (`mkctl_bb1m_oracles.py`):
- The generator is the worker's generator, with the covering-subset choice replaced by `Oracles`' own seal records and only the 7 reader rows kept.
- I ran it for strict and coe, A and B, sealed and unsealed: 8 probes.
- Each sealed probe fails exactly the 7 negatives (`ctlOracleZero/One/Two`, `ctlEncPP`, `ctlEncSK`, `ctlMsgSpace`, `ctlSimCt`) once each. All 7 `Reader` positives pass, and the unsealed probes have 0 errors. **ALL_OK True in both variants.**

**Scan:** 947 items, **0 foreign**. The kinds probe has rc 0.

**Cross-build X = tip × #346 × #340** (`b90b966b`), advanced in the same output from the checked M state:
- **Build.** The plan has 13 to build: `Pairing/Assumptions` and its downstream, which is `Pairing`, `KeyExchange/Joux`, `KeyExchange`, `Words`, `Handler`, `Reduction`, `Oracles`, `BonehBoyenMachine`, `BonehBoyenSecurity`, the two facades and the root. That set equals `downorder.py`'s.
  - **13/13 rc 0, 0/0 errors.** `Pairing/Assumptions` has 0 warnings, and `BonehBoyenSecurity` has exactly 2 `sorry` warnings.
  - The state check over 1426 modules is OK, the link count is 1 for all 13, and snapshot #2 rehashed 0/0/0 afterwards.
- **Admissions.** Tip 196 → X 194, **−2: exactly T4 and T1** (`Pairing/Assumptions` 1 → 0). Over the issued closure, 22 → 20.
- **Axioms.** **T1 `bdhAssumption_of_dbdhAssumption` is standard**, `[propext, Classical.choice, Quot.sound]`, and reaches 0 sorried constants. T4 is unchanged and standard. **`bb1_sidSecure` still reaches exactly T2 and T3.** The census still has 0 non-standard.
- **#340 seals.** These are the canonical coe A and coe B on `Pairing/Assumptions`, run with int-x-341-340's steps and pair-bdh's tools, which are byte-equal to mine.
  - **coe A has 894 requests and coe B 895. Both have rc 0, 0 `error:`, 0 `error(`, install and EOF records, and no failing declaration.**
  - The collector source and log, both probe sources and both summary rows are **byte-identical** to int-x-341-340's. The owner's 58-module closure is blob-equal at X, at #340's head and at int-x's B.
- **The 5 #346 owners whose closure contains `Assumptions`**, under strict and coe, A and B (20 seals): all have rc 0 and 0/0 errors.
  - Each request count is the snapshot-#2 count +2. The extra rows are exactly #340's private definitions `Pairing.tupleBdh` and `Pairing.tupleTgt`, in `Pairing/Assumptions`.
  - No other row changed.
- **Not built on snapshot #4.** The X cross-build was not repeated on #4; the coordinator's instruction was to replay #346 alone. Since then the closure of `Assumptions` has changed by #352's three theorems in `Pairing/Group`; no definition was added.

**Output map at X.** Before deletion, the output's map was `olean-replay-346.map-X-b90b966b.noMathlib.tsv`: 1457 entries, SHA-256 `427fd000…f27a` (with NthRootLemmas: `26570749…6b27`). The coordinator then asked me to delete `$SP/olean-replay-346`, because it could not be adopted after #351, and I deleted it.

## Snapshot #3 (`supporting-346b-snapshot3/`)

These are supporting results only.
- `cp -al` of #3, with 0/0/0 before.
- Tree `2acfdbcd`: 12/12 rc 0, 0/0 errors. The state check over 1427 modules is OK, the link count is 1 for all 12, and #3 rehashed 0/0/0 after.
- The oleans are byte-identical to snapshot #2's, and the axioms log is byte-identical.
- Admissions: tip 198 → 197, which is −1 (T4).
- The 32 regenerated seal records are row-identical, with probes byte-identical. The lint is unchanged.
- Map `738957ab…` (no-Mathlib `0f57710a…`).
- I deleted `$SP/olean-replay-346b` when the coordinator asked, after #352 merged.

## Anomalies and disclosures

1. **Container restart at about 01:30 UTC.** It killed the snapshot-#2 seal and control run at 77/80 probes, before the `Oracles` controls and the scan.
   - I set the partial outputs aside, untrusted (`interrupted/README.txt`; only their `results.jsonl` and the driver logs are kept).
   - I removed the stale probe sources.
   - I re-ran statements, collector, axioms, seals, controls, the `Oracles` controls and the scan from scratch. The re-run collector and axioms logs are byte-identical to the pre-restart ones.
2. **Snapshot advances.** Snapshot #2 was retired at the #351 merge, and #3 at the #352 merge, as the coordinator announced. My last check of each was 0/0/0: #2 at 02:50 UTC, #3 at 03:26 UTC. After each was retired I did not rehash it, as the coordinator asked.
3. **NthRootLemmas in 346c.** The first `mathlibextra.sh` call used a relative log path from another working directory. The redirections failed and `lean` did not run, so nothing was written; the olean was absent afterwards. I re-ran it with an absolute path, and it gave `c0a9cff0…`. The note is in `build-mathlib-extra/NOTE.txt`.
4. **Driver edits.**
   - `rule10_346.sh` gained `TREE_OVERRIDE`, `TIP_OVERRIDE` and `TMPDIR_OVERRIDE`, which select the tree and the tip; its defaults are unchanged.
   - The seal sources are taken through `GIT_DIR` from `git archive` exports. The worker-side harness (`rule10_b.sh`, `mkseals_*`, `ctlcheck2`, `sealsum`, `scan*`) ran unmodified.
5. **`touched-after.json`.** It was built against the tip rather than `9e7a9648`. It is used only to attribute a failing line to a declaration, and there were none.
6. **No restore.** The snapshot directory was never written: every base rehash is 0/0/0. The Mathlib overlay stays in `olean-replay-346c/Mathlib`, and recipe step 6 removes it at adoption.
7. **Concurrency.** Other agents' Lean processes ran on their own trees (`olean-replay-bb1sim-group`, `olean-replay-352`). Mine ran one at a time, and I did not touch their directories.

## Files

- `phase2-evidence.zip`: see `SHA256SUMS` for its hash. Under `bb1-machine-r1-phase2/` it holds:
  - `PROVENANCE.txt`;
  - `final-346c-snapshot4/`;
  - `supporting-346b-snapshot3/`;
  - `supporting-346-snapshot2/`, which includes `x/` and `interrupted/`;
  - `tools-used/`.

  It also holds its own `SHA256SUMS`, which covers every entry.
- `SHA256SUMS` lists the zip and this README.
