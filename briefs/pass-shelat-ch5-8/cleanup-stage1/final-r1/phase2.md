# cleanup-stage1 · phase 2: merged-tree Lean replay and checks (PR #355 stacked on #347)

**Verdict: PASS.** The prospective tree TS1 = records tip × #347 × #355 builds cleanly on olean snapshot #5. The checks at TS1 match the recorded effects of #347 and Stage 1 exactly:
- admissions +0;
- axioms standard;
- Rule 10: no seal failure in a new or changed declaration in the coe variants; the strict-only failures are the `FinDist` coercion (notation); every other failure is pre-existing and identical at the tip; controls ALL_OK;
- lint unchanged except the removed `Trapdoor` WARN.

**#347 and #355 are ready for Gate 47.** The replay `$SP/olean-replay-cs1` is kept as the snapshot candidate.

- Date: 2026-11-17 UTC, 07:43–11:10. `$SP` is the maintainer scratchpad, as in `maintainer/snapshots.md`.
- One Lean process at a time, through `scripts/lean_check_tree.sh` (build) or the recipe's `runner_full.py` (probes: `lean -DmaxErrors=0`, no `-o`).
  - Watchers logged the host Lean count every 30 s. The maximum observed was 3, so nothing was paused.
  - The lowest free disk was 2200 MB.
- No `lake build`, no cache get. Nothing was committed or pushed, and no PR was edited.
- Evidence: `cleanup-stage1-final-r1-phase2-evidence.zip` under `cs1-final-r1-phase2/`, with its own `SHA256SUMS`. Its SHA-256 is in `evidence-SHA256SUMS`.

## Inputs
| What | Value |
|---|---|
| Records tip (fetched by name) | `e1d39836ed4a69a34914c35f4c73c71de853dcc6`. 0 Lean, toolchain, manifest or lakefile files differ from `3f540c22` (snapshot #5's T) |
| Snapshot #5 | `$SP/olean-snapshot`. Map `olean-snapshot.map-3f540c22.tsv`, SHA-256 `fca1b6a308ac1585fb5897fae95e8294b54be55e160119e4eca1702692b41ef9`, equal to the records copy. Files manifest `12457f32…`, equal to the records copy. 1458 entries |
| #347 | `daa6e173cdd94cad1475b9a96eca613bce53ba61` (`cleanup/dw5-derand-readers`) |
| #355 | `d3c7cb00092ad5913904654d922f30fc7d5fce4a` (`land/cleanup-stage1`), tree `508f915413ee8ef9f2a37b59e0012c9daf3867aa`. #347 is its ancestor |
| Recipe tools | `$SP/snaptools3/olean-advance-a6d01b1b/tools-used/`, read only (hashes in `tools/recipe-tools-used.sha256`) |

## 1. Prospective tree TS1
- `git merge-tree --write-tree`, all clean, in every order:
  - (tip × #347) × #355;
  - tip × #355;
  - #355 × tip;
  - #355 × (#347 × tip);
  - (tip × #355) × #347.

  Every order gives **TS1 = `1eaf940b938bb52e3919f5569893b58522df599b`**. tip × #347 is `f905d841…`.
- **TS1 against the tip:** exactly the 23 Lean files of #347 and #355, +1,332/−296. That is #347's +253/−296 plus Stage 1's +1,079/−0, and no other file.
  - Every file is blob-equal to #355, except `Games.lean`. That file is the union of the tip's `Relational` import and entry and #355's `Tapes` import and entry.
- **TS1 against the phase-1 tree `5a2e818d`:** the Lean difference is exactly #340's and #346's 9 files, each blob-equal to T `3f540c22`:
  - `Pairing/Assumptions`;
  - `IdentityBased/{BonehBoyen, BonehBoyenMachine, Defs}`;
  - the 5 new `BonehBoyenMachine/{Draws, Handler, Oracles, Reduction, Words}`.

  The other 31 differing files are records only.
- The tree was exported from TS1 with `git archive`: `TCSlib`, `TCSlib.lean`, `audits`, `scripts`, the toolchain, the manifest and the lakefile. `.lake/packages` is a symlink to the repository's.
  - The path set equals the tree: 1463 `.lean` files, all blob-verified.
- Intermediate trees for the three-way orders were passed as unreferenced temporary commit objects (`git commit-tree`, no ref).

## 2. Replay (recipe steps 1–5)
- **Copy and overlay.**
  - `cp -al $SP/olean-snapshot $SP/olean-replay-cs1`.
  - `mloverlay.sh` gave 3346 symlinks.
  - `mathlibextra.sh` compiled NthRootLemmas to olean `c0a9cff04c6707edac6980cf4d3c3cc8116ab8843e9ddfb82f6688aee8e0f54c`.
- **Plan.**
  - `stateplan init` at T over the #5 manifest keyed 1427 modules.
  - `downorder`: changed 23, down 556, order 1429.
  - `fullorder`: roots `TCSlib` and both `audits/*/Checks`, **full order 1429** (1427 + `Games/Tapes` + `ZeroKnowledge/InteractionWords`).
  - `stateplan plan`: **build 556**, reuse 873. The queue is exactly `down`.
- **The 556 against the review's 551:** the 551 plus #346's 5 new `BonehBoyenMachine/*` modules, which now lie downstream of #347/#355 in the tip. Nothing is missing (`plan/queue-vs-review-551.txt`).
- **Build:** `runner.py` with `TCSLIB_OLEANS=$SP/olean-replay-cs1`, 07:47–08:43 UTC.
  - Module time was 3364 s; the longest was CookLevin/Hardness at 309 s. Max RSS was 4.55 GB.
  - **556/556 rc 0.** `error:` 0, `error(` 0, the substring "error" 0. 26 sorry warnings, 272 warnings. `permod`: 0 log/record mismatches.
- **Accept:**
  - `stateplan update`: 556 modules, none refused.
  - `check` over the 1429: **1429/1429 OK, RESULT OK**. This was re-run after all probes, and the result is the same.
  - **Link count 1 on all 556 rebuilt oleans,** after the build and again after the probes.
  - The 873 reused oleans are hard links of the snapshot's.
  - No `.ilean`, and no symlink outside `Mathlib/`.
- **Snapshot #5: `snapmap verify` gives 0/0/0, RESULT OK,** at three points:
  - before the copy;
  - after the build;
  - after every probe.
- **Replay directory state:** `$SP/olean-replay-cs1` (1.4 GB apparent, mostly hard links).
  - It holds 1460 oleans: the 1429 of the closure plus 31 PFR. It also holds the `Mathlib/` overlay (3346 symlinks and the NthRootLemmas olean).
  - The checked state is `plan/state-after-update-1eaf940b.json.gz`.

## 3. Checks at TS1
### Admissions (against the tip)
- `tipcensus.py` over the campaign's record sets plus this replay's records gives **196 at T and 196 at TS1, identical module by module**.
  - The only rows that differ are the two new modules, absent → 0.
  - The 556 rebuilt modules carry 26 sorry warnings at both revisions.
- Source scan: the tip → TS1 Lean diff adds and removes 0 `sorry`, `admit` or `native_decide` tokens.
- This matches **#347's recorded effect** (DW-5: 229 → 229 at its own tip, identical per module, 0 in its three files) and Stage 1's (+0 against `base-sorries`).
- Note: #346's `Draws`, `Handler` and `Words` had no earlier build record. Their T count comes from this replay, whose sources equal T's.

### Axioms (`axioms/`; one probe on the replay)
- **Stage 1's 69:** all within {`propext`, `Classical.choice`, `Quot.sound`}. The split is **34/12/6/4/13**, the recorded one.
- **#347's 27** (DW-5's list: the 9 readers, E1 `computesFunInTime_find`, `polyTimeComputable_find` and the derand chain down to `bpp_subset_dtime_subexp`): all exactly the standard three.
- **Census of every constant in the 21 owners:** 1224 constants, all standard. No `sorryAx` anywhere, and 0 errors.
- The 80 touched declarations from the tip to TS1 are all covered:
  - 69 Stage 1 additions;
  - #347's 9 readers;
  - #347's 2 re-derived proofs (`computesFunInTime_find`, `polyTimeComputable_find`, CHANGED).

### Rule 10 (`rule10/head`, `rule10/tip`; driver `tools/rule10_cs1p2.sh`)
- **Owners: 21.** These are Stage 1's 17 changed owners, its 2 new modules, and #347's `ModuleHost` and `IterateFind` (`IterateFindHost` is shared).
  - The facades `Games.lean` and `ZeroKnowledge.lean` gain only an import and a doc line. They hold no declaration, so they are not owners.
- **Method:**
  - canonical seals A/B, strict (`mkseals_ab`) and coe (`mkseals_coe`, which excludes `FinDist.instCoeFunForallReal`), with the archived Gate 06/10 instrumenter;
  - B seals `PolyExpr.eval` as well;
  - the same probes also ran at the **tip on snapshot #5**, read only, for the 19 owners that exist there.
- **Head = the recorded seals.**
  - All 76 Stage 1 rows equal the worker's delivered head (`seals-*.tsv`: requests, rc, errors, install, EOF and the failing-declaration set).
  - All 12 #347 rows equal DW-5's head.
- **No failure in a new or changed declaration in either coe variant** (0 of 80 touched).
- **Strict-only failures in new declarations:** 16 errors (8 per strict variant), in six `FinDist` declarations:
  - `Entropy`: `mixture`, `mixture_apply`, `mixture_isSource`;
  - `Samples`: `map_apply_expect`, `map_map`, `map_prod_snd`.

  In every owner, strict A's requests minus coe A's are either empty or exactly `FinDist.instCoeFunForallReal`. **By ruling (DW-10 Q3; CS1-Q3 / CS1-W2) the coercion is notation:** recorded, no fix.
- **B-only failures** (strict B's requests minus strict A's are either empty or exactly `PolyExpr.eval`, notation by ruling):
  - `PPT` `runAtL_ofPolyTimeUniform`, 1;
  - `EnsembleSecurity` `singleMessageSecure`, 2;
  - PRF `Asymptotic/Defs`, 8.

  None of these is in a touched declaration.
- **Pre-existing, identical at the tip** (same declarations and counts in the tip run):

  | Owner | sA/sB/cA/cB | Failing declarations | Item |
  |---|---|---|---|
  | `IterateFindHost` | 16/16/16/16 | `copy_*`, `host_dispatch`/`branch`/`halt` | DW-9 |
  | `ModuleHost` | 10/10/10/10 | `stop_*`, `clean_*`, `pad_*`, `host_seam`, `host_call` | DW-9 |
  | `Trapdoor` | 3/3/3/3 | `acceptProb_owpGen*_unit`, `predProb_pkPredictor_eq` | pre-existing (phase-1 table) |
  | `Entropy` | 10 → 15 strict; 5/5 coe | coe: `IsFlatSource.isSource`, `isSource_uniform`, `le_minEntropy_iff`, unchanged (CS1-F07); strict: the pre-existing coercion rows plus the three new `mixture*` above | DW-10 |
  | `PPT`, `EnsembleSecurity`, PRF `Defs` | B only, as above | as above | notation |
- **Tip → TS1** (`cmp/head-vs-tip.txt`): 56 of 76 shared rows are identical. The 20 differences are all explained:
  - **`IterateFind` 20 → 0 in all four variants:** #347's F-01 clearance, reproduced on the merged tree.
  - **Requests:** `Adversary` and PRF `Defs` +3 (`recordBits`, `recordBits.match_1`, `zipWith_xor_cancel_right.match_1_1`).
  - `EncodingMachines` −3 net: #347's re-derivation drops `polyTimeComputable_find`'s four matchers and splitters and adds `computesFunInTime_find.match_1`. That equals the worker's base (#347 head) → head.
  - The new strict-only rows in `Entropy` and `Samples` above.
- **Paired controls:**
  - Stage 1 (`mkctl_s1.py`, `controls-spec.json`, blob ids in `tools/blob-ids.txt`):
    - 38 probes per variant;
    - **20/20 sealed negatives fail exactly once**, in strict and in coe;
    - 0 positives fail, unsealed rc 0, 0 stray errors, install and EOF on all 19;
    - ALL_OK, and identical to the worker's `ctlcheck` (labels, rc, per-control errors).
  - #347 readers (DW-5's `mkctl_dw5.py`): 10 probes per variant, **30/30 negatives fail exactly once**, ALL_OK in strict and coe.
    - DW-5 had 8 probes and 29 negatives. The covering seal records are now chosen over 21 owners (PPT's B record carries `PolyExpr.eval`).
- **Explicit-unfold scan** (21 owner files, touched = tip → TS1):
  - **438 items in the 80 touched declarations, 0 foreign.** That is 310 in the 69 Stage 1 additions, equal to the worker's 310, and 128 in #347's CHANGED proofs (all in E1 `computesFunInTime_find`), equal to DW-5's 128.
  - The 2 owned-definition items are `Games.extTape` in its own readers.
  - The foreign multiset (29: 27 `IterateFindHost` `copy_*`/`host_branch`, 2 core/Mathlib in `Entropy`) is **identical** at the tip, the worker's head and the worker's base.

### Lint (against the tip; same scripts at both)
- **`campaign_style_lint --check8b`,** FAIL/WARN line multisets with line numbers dropped:
  - Cryptography 92/104 → 92/103: the only change is the removed `Trapdoor` `pkPredictor` WARN;
  - InformationTheory 5/2 → 5/2;
  - Complexity 25/390 → 25/390.

  No new line.
- **`style_lint` on the 23 files:** 2 findings, both pre-existing at the tip on the 21 existing files:
  - `BitLists` `## References` placeholder;
  - `Strings` `canonFun_poly`, line 414 → 425.

## 4. Disclosures for Gate 47's pack
1. **The tree is TS1 `1eaf940b`, not the review's `5a2e818d`.** The tip now holds #340 and #346 (9 Lean files, blob-equal to T), so the rebuild is 556 modules: the 551 plus #346's 5 new modules.
2. **Pre-existing Rule-10 failures carried on the touched owners,** identical at the tip:
   - DW-9: `ModuleHost` 10 and `IterateFindHost` 16;
   - `Trapdoor` 3 (pre-existing) and DW-10's `Entropy` coe 5;
   - B-only `PolyExpr.eval`: PPT 1, EnsembleSecurity 2, PRF Defs 8.
3. **Strict-only failures in six new `FinDist` declarations** (16 errors): the coercion, which is notation by ruling. coe variants: 0.
4. **#347's effect reproduces on the merged tree.** `IterateFind` goes 20 → 0 in all four variants. The admissions and axioms are as recorded.
5. **DW-5's control harness gives 10/30 rather than 8/29.** The covering choice is over 21 owners; it is ALL_OK.
6. **GSW 6a is not in TS1.** P2-6's cross-build for #340/#346 is subsumed, since both are in TS1, and it was not run for 6a. Its intersections (root, the `CircuitComplexity` facade, `ComputationalModels`) mean that whichever of 6a and Stage 1 merges second re-replays.
7. **Process:**
   - The tip seal run's first attempt stopped before any Lean ran, because the tip export lacked `lean-toolchain`. It was rerun after adding the file (`rule10/tip-first-attempt-driver.out`).
   - The seal-phase watchers' process pattern matched themselves, so they outlived their drivers until I killed them. They only log, plus pause on more than 3 Lean processes, which never happened.
   - Three temporary unreferenced commit objects were created for merge-tree inputs.

## 5. Adoption (recipe step 6)
`$SP/olean-replay-cs1` is the snapshot candidate **only if a merge commit's Lean equals TS1 `1eaf940b`**. That is the case when #347 and #355 have both merged and nothing else has changed Lean.
- If #347 merges alone first, its merge is not TS1. Adopt only at #355's merge, after the step-3 diff against TS1 is empty.
- If any other Lean change (for example 6a) lands in between, discard the replay and replay again.
- At adoption: remove `Mathlib/`, make the map and the manifest, run `basecheck`, swap, verify 0/0/0, and add the `snapshots.md` row.

**Ready to run: Gate 47 on #347 + #355.** Merge stays with Seyoon after Gate 47 clears.
