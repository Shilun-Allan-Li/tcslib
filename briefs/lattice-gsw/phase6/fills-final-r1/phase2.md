# gsw-6a-fills · final r1 · phase 2: the 6a landing branch on olean snapshot #6

**Verdict: PASS.** All checks hold, so the branch is pushed and a draft PR is open (see the end).

- **Branch:** `land/gsw-6a-fills`, head `ccca6f804552f72b400c09e7a3bd694371bdf568`, on the records tip
  `036d823933c8248bd8894c7963e15dd0f1837075`. That tip is Lean-equal to snapshot #6's T `8060f6b7`: 16 commits, 0 Lean,
  lake, scripts or audits paths.
- **Coverage:** all 98 6a targets are proved, with 0 `sorry` in the 13 6a modules. Library admissions stay at 192, equal
  module by module to snapshot #6. The axioms are standard and no `sorryAx` reaches anything.
- **Rule 10:** 0 new failures, the paired controls are ALL_OK, and the scan finds 0 new foreign unfolds.
- **Landing edits:** all four landed. LE-gf4 compiles, so it was kept.

Maintainer sub-agent, 2026-11-17. Work directory: `$SP/g6aland`. Replay tree: `$SP/olean-replay-6a-land`.

## Branch shape

All first-parent commits are signed (19 of 19 have `gpgsig`). Signature verification is not possible on this host,
because no allowed-signers file is configured.

The maintainer commits end with the two required trailers. The worker's 7 cherry-picks keep their own messages
unchanged, so they carry the worker's session trailer and not ours. Paths were staged explicitly.

| # | Commit | Content |
|---|---|---|
| 1 | `49f88fef` | signed `--no-ff` merge of #358 `a616adca` |
| 2 | `76efe1ba` | signed `--no-ff` merge of #359 `d154c883` (LE-g45, LE-g45b). The Lean paths equal g6a-s6's R2′ tree `901bf528` |
| 3 | `32ec2ef5` | signed `--no-ff` merge of #360 `cc05f76c` (+79, 6 files) |
| 4 | `40c7215c` | **#360 addendum 2, LE-gf3 part 1.** `Basic.lean` gets `TreeCircuit.maxDepth_le_of_forall` and `maxFaninL_le_of_forall`. `Adder.lean` gets `prefixVal_eq_of_false` and `prefixVal_testBit`. All four are public, with the worker's bodies verbatim and docstrings that state the formula and say "Glue." (+36) |
| 5 | `c7fb15ee` | **U1/U2** `Defs` and `Eval`: the blobs of `f31382a5` (`3d2aed4a`/`668c04a3`). Neither file changed in #359 after `73aedcda` |
| 6 | `bec8eefd` | **U3** `Barrington`: the in-house diff `73aedcda→f31382a5`, three-way merged onto #359's file (`git merge-file`). It merged clean, and the applied diff equals the in-house diff (449 = 449 lines) |
| 7 | `2ddada22` | **U8** `Combinators`: `73aedcda→b65668a9`, three-way merged onto #359. The one conflict was `const_eval`'s body; **LE-g45's** `rw [TreeCircuit.const_eq]; exact eval_node_nil b x` was kept. The applied diff is the in-house diff minus that 5-line hunk |
| 8 | `e0d3e537` | **U6** `NANDForm`: the blob of `b65668a9` (`f0efb6ef`) |
| 9–15 | `e2b7020c`, `2f38e2b9` (U4); `80de2e4e` (U5); `72bfcab0` (U9); `1bf78b47` (U10); `153811f1` (U11); `bf8aef14` (U7) | `cherry-pick -S` of `f437e0d0`, `bb7efa82`, `59599399`, `9edc2be0`, `aa442e1d`, `9603797e`, `c8f2d23f`. **range-diff 7/7 `=`**. After step 15, the 6 external files are blob-equal to `bb7efa82` |
| 16 | `91e2f807` | **LE-gf1**, `NC1` (+5/−8) |
| 17 | `c1a444f2` | **LE-gf3 part 2**: 14 private copies deleted, CarrySave's two `*_getD_le` made public, uses qualified (+36/−168) |
| 18 | `22636300` | **LE-gf2**, the `layerNAND` docstring (+3/−2) |
| 19 | `ccca6f80` | **LE-gf4**, `ModSum` F9 (+6/−6). **Kept: it compiles** |

- **Reproduction:**
  - `issued-fills-r1/tools/mkbase.sh` prints `BASE 05999162… tree 7d551d6f…`.
  - Each of the 7 patches of exchange `60703442` was applied with `git am`, using its `COMMITS.tsv` committer identity
    and date, in a temporary sparse worktree that was removed afterwards. They reproduce all 7 hashes (`repro/`).
- **Landing edits:**
  - They are the recorded `landing-edits-proposed.diff` (`01c07a11…`), split per edit and file (`tools/splitle.py`,
    `le/`). Every hunk applied cleanly.
  - The 8 edited files at the head equal `bb7efa82`'s files with the whole recorded diff applied, 8 of 8
    (`log/le-apply-equal.txt`).
  - Size: the review's summary says LE-gf3 is +68/−154. The recorded diff itself is +72/−168: the addendum is +36,
    part 2 is +36/−168.
- **Stack:**
  - `git diff 32ec2ef5 HEAD` touches exactly the 13 unit and edit files.
  - `git diff tip HEAD` touches 24 files, 23 of them `.lean`; the other is `machine-library-design.md` from #359.

## Replay on snapshot #6

| Check | Result |
|---|---|
| Snapshot #6 (`0858dccb…`) | rehash **0/0/0** at the start, after the build and at the end |
| Copy | `cp -al $SP/olean-snapshot $SP/olean-replay-6a-land`; `mloverlay.sh` (3346 symlinks); `mathlibextra.sh` NthRootLemmas `c0a9cff0…` (lean rc 0) |
| Mathlib imports | the 6 new ones (`Data.Fintype.BigOperators`, `Algebra.BigOperators.Fin`, `Algebra.Order.BigOperators.Group.Finset`, `Data.List.MinMax`, and the in-house `Algebra.BigOperators.Group.Finset.Piecewise` and `Algebra.Order.BigOperators.Group.List`) are all in the pinned package build (3346 oleans). They resolved |
| Export | `wtx` = `git archive ccca6f80`, checked blob for blob (`exportcheck.py`): 1597 files, 0/0/0 |
| Plan | `downorder.py` against the tip: 23 changed, 579 downstream. `fullorder.py`: 1445. `stateplan.py` init at `8060f6b7` (1432) then plan: **build 564** (551 existing + 13 new), reuse 881 |
| Not built | 15 modules of `down.txt` are outside the root/Checks closure, so they are not in the snapshot (RazborovSmolensky ×13, LMN `LMNConcentration`, `LayerReductionHelpers`). None of the six new or now-public names occurs anywhere in TCSlib or audits outside its home (grep), so they cannot clash there |
| Build | `run-build-land.sh`, one module per call through the recipe's `runner.py`. The queue was reordered imports-first so that the 27 modules up to the 6a facades ran first (`frontload.py`, checked as a permutation and imports-first). There were no slot waits, and the disk guard (1.5 GB) never fired. 16:46–17:34Z, 2833 s of compile time |
| Result | `permod.py`: **564 modules, rc≠0 0, `error:` 0, `error(` 0**, 0 log/record mismatches. Sorry warnings 103, warnings 205 |
| State | `stateplan update` (564 taken), then `check` over 1445: **RESULT OK** (`state.json` `28bfa05d…`) |
| Links | 564/564 rebuilt oleans have link count 1, and each hash equals its record |
| Warnings | `warncmp.py` against the g6a-s6, LE-g48, olean-advance, rebase-2 and bootstrap logs: **540 SAME, 0 DIFF**, 24 NEWSRC (new or changed sources, every one with 0 warnings) |
| Output map | Mathlib excluded: 1476 entries, `5f48b3e4…`. Against #6: 1453 equal, 10 changed (the 6a-touched owners, the facades and the root), 13 added. The other 541 rebuilt oleans are byte-identical |

## Admissions

- **6a files:** the syntactic scan (`sorryscan.py`) gives 97 targets in 11 modules at #359 `d154c883`, and 0 at the
  head. Every 6a module built with 0 `sorry` warnings and 0 warnings of any kind. The 98 targets are those 97 plus
  `const_eval`.
- **Library:** the syntactic scan over the full order gives **192 in 44 modules** both at `8060f6b7` (1432 modules) and
  at the head (1445). The per-module lines are identical.
- **Build cross-check:** the 564 rebuilt modules have 103 `sorry` warnings, equal per module to the scan. The 881
  reused modules hold the other 89.

## Axioms

Probe `AxiomsLand.lean`. Its body is the statement phase's census of the 13 6a modules and TreeNCAC, unchanged, with
`#print axioms` lines added. It ran with rc 0 (`checks/axioms-check.txt`).

- All **98 targets** depend only on `propext`, `Classical.choice` and `Quot.sound`, with every name resolved uniquely.
- The census covers 859 constants: 0 non-standard axioms, **0 TRACE lines**, and no `sorryAx` anywhere.
- These are standard as well: `layerNAND`, `layerNAND_gates`, `layerNAND_output`, `toNANDForm`, `const_eval`,
  `eval_node_nil`, and the six LE-gf3 public lemmas. `prefixVal_eq_of_false` depends on `propext` only.

## decls2 (pinned `fa81981a…`) against the tip `036d8239`

**289 ADDED, 1 REMOVED, 0 CHANGED** (`decls2/`).

- ADDED is exactly #359's 268 (including #358) plus #360's 15 (decls2 of each PR against its own base; the union
  equals tip→`32ec2ef5`), plus the 6 public lemmas.
- The 6 public lemmas are `TreeCircuit.maxDepth_le_of_forall`, `TreeCircuit.maxFaninL_le_of_forall`,
  `prefixVal_eq_of_false`, `prefixVal_testBit` and `FormulaArith.depth_getD_le`/`maxFanin_getD_le`. They are exactly
  `32ec2ef5`→head.
- REMOVED is `BoolCircuit.eval_node_nil` from `Hierarchy`; it is ADDED in `Combinators`. This is LE-g45's move.
- decls2 strips comments and docstrings, so **LE-gf2 (the docstring exception) is not tracked**. No fill changed a
  public statement.

## Rule 10

### Canonical coe-A seals

22 owners, from the `land` series of `tools/rule10_land.sh`. Every Lean process ran through `gated_full.sh`.

| Owner | Requests | Errors | Recorded runs |
|---|---|---|---|
| BranchingPrograms (facade) | 339 | 0 | #5 statements: 335/0 |
| Barrington | 119 | 0 | #5 statements, LE-g45/45b, fill12: 119/0 |
| BarringtonConverse | 243 | 0 | 243/0; worker head 243 (same set) |
| Defs, Eval | 0, 25 | 0, 0 | equal |
| NC1 | 337 | 0 | #5 statements: 333/0; worker head 336 (+`barrington_recognizes.match_1_1`, from in-house U3) |
| CircuitComplexity (facade) | 3738 | 0 | #5 statements: 3726/0 |
| FormulaArith (facade) | 283 | 0 | #5 statements: 276/0 |
| CarrySave, Compare, ModSum | 253, 275, 280 | 0 | worker head: the same sets |
| Combinators | 174 | 0 | equal (all records) |
| NANDForm, NANDLayering | 180, 187 | 0 | equal |
| ComputationalModels | 1106 | 0 | equal |
| Basic, DAGCircuit | 0, 0 | 0 | equal (#360 readers) |
| Adder | 58 | **3** | #360 readers: 58/3, the same declarations (pre-existing) |
| DAGTransform | 174 | **11** | #360 readers: 174/11, the same declarations (pre-existing) |
| TreeDAG | 141 | **25** | #360 addendum: 141/25, the same declarations (pre-existing) |
| TreeNCAC | 218 | **2** | #5 statements and #6 o1: 2, the same declarations (`maxDepth_map_le`, `maxFaninL_map_le`; G6A-F05) |
| Hierarchy | 355 | **2** | LE-g45: 355/2, the same declaration (`InTreeSize.inSIZE`) |

Every probe has its install and EOF records. Every failing declaration is in a recorded run's failing set, so there
are **0 new failing declarations** (`rule10/sealcmp.txt`, `rule10/vs-worker-final-head.txt`).

### Root coe-A

`SealA_Root` (owner `TCSlib`, `root` series): **14,098 requests in one probe (chunked at 1000), rc 0, 0 errors**,
install and EOF records present; 17:52–18:56Z. The #5 statement run had 14,074 requests and 0 errors.

### Paired controls

Generated by `tools/mkctl_g6aland.py`, which is the 6a harness with new rows.

- **Rows:** one per public lemma.
  - The negative proves an instance by a defeq read of the definition the lemma is about:
    - `TreeCircuit.maxDepth`, `maxFaninL`, `prefixVal` and `prefixVal` (`Nat.le_of_eq rfl`, `decide`);
    - `TreeCircuit.const` for both getD lemmas (`have … := rfl`).
  - The positive proves the same instance through the public lemma.
- **Seals chosen:** Barrington's seal (for maxDepth and maxFaninL) and CarrySave's seal (for the prefixVal, const and
  getD rows; the getD rows are restricted to owners that have CarrySave in their closure).
- **Result (attempt 2): ALL_OK.**
  - Sealed: each of the 6 negatives fails exactly once, all positives pass, and the install and EOF records are
    present.
  - Unsealed: all pass, with rc 0.
- **Attempt 1:** the two getD positives left the list `U` to unification, so `nomatch h` hit "Missing cases" both sealed
  and unsealed. This was a defect in the control statements, not a module finding. It is fixed by `(U := [])` and kept
  in `rule10/land/controls-attempt1/`.

### Explicit-unfold scan

The scan covered the 22 changed files under `TCSlib/`, at the head and at the tip. The tip's kinds probe was run
read-only against snapshot #6. Its first run lacked `lean-toolchain` in the export and is kept as `runs-attempt1-no-toolchain`.

- **0 foreign unfolds at the head that are not at the tip** in the same file, declaration, name and tactic. The three
  `TreeNCAC.toBinary_*` `simp [TreeCircuit.maxFanin/size/depth]` items count as touched only because O1 changed those
  declarations; they are at the tip too.
- 3 foreign unfolds are removed: LE-g45's `eval_node_nil`, and O1's `combineFuel_eval` and `eval_node_pairUp`.

## Lint, sizes, duplication

- **Lint:**
  - `campaign_style_lint --check8b` (blob `88a2256b`): 25 FAIL / 390 WARN at the tip (500 files) and at the head (513
    files). The FAIL sets are equal. The 4 changed WARN lines are shorter check-8 lists (Adder, DAGCircuit,
    DAGTransform, TreeNCAC: #360's readers). There are no new FAIL or WARN lines.
  - `style_lint` (blob `87cb27d0`) on the 23 changed files: the same 14 findings as the tip's 10 existing files (one
    TreeDAG line number moves +10). 0 added lines over 100 characters.
- **Sizes:** Barrington 895, BarringtonConverse 533, Defs 479, Eval 221, NC1 263, Combinators 768, CarrySave 638,
  Compare 499, ModSum 416, NANDForm 520, NANDLayering **948**. GF-W3 accepted 947, and LE-gf2's rewrap adds one line.
  All files are under 1,000 lines.
- **Duplication sweep** (`tools/dupsweep.py`, `dup/sweep.tsv`): the 6 public lemmas plus all 75 private helpers left in
  the 6a files, searched by short name in TCSlib, audits, Mathlib `029db123`, Batteries and core v4.25.0, and by
  normalized body.
  - The public lemmas have no other declaration of the same name anywhere.
  - No two helpers have the same body.
  - The name hits are not duplicates:
    - `IsFiveCycle.isCycle`, `.orderOf_eq` and `.apply_ne` are glue over the Mathlib lemmas of those names (other
      namespaces);
    - Barrington's private `isPermutation_ofPerm` is the program-level lift that cites Defs' public
      `Instr.isPermutation_ofPerm`;
    - `pairUp` is a Mathlib tactic-internal name.

## Disclosed items

1. **Stale in-house frozen docstrings** were left, because no ruling covers them. They are for a docstring follow-up
   like LE-g45b:
   - `Defs:32`, `Eval:35` and `Barrington:32` say "targets admitted with `sorry`";
   - `NANDForm:61` and `:455` say "While N2 is admitted, `sorryAx` reaches `toNANDForm`".
2. LE-gf3's line count: see "Branch shape".
3. The in-house units (U1–U3, U8, U6) were not reviewed beyond these phase-2 checks. That includes their sketches and
   helper set; their duplication was covered by the sweep above.
4. **Superseded trees deleted:** `olean-replay-6a-fill12`, `-6a-fill86` and `-6a-readers`, at 17:25Z.
   - Why: free disk was 1613 MB with about 90 modules left.
   - How: by literal path, after checking that no process used them and that they held only 49 MB of unique files.
   - Effect: free disk 1613 → 1669 MB (`log/deleted-trees.txt`).
5. **Tip moved.** #347/#355 (cleanup Stage 1) merged while this ran; the tip is now `acd66709`, Lean-equal to TS2
   `13fc8060`.
   - The coordinator's update arrived after the build and the seals were done, so the branch stays on `036d8239` and
     the replay on #6.
   - `git merge-tree acd66709 ccca6f80` is clean (rc 0), and no file is shared.
   - 3 tip-changed modules lie in this branch's rebuilt set: `Cryptography/Games`, `Cryptography/ZeroKnowledge` and
     `Encryption/PublicKey/Trapdoor`.
   - **Follow-up:** before merge, re-create or merge the branch on the new tip, and re-replay on snapshot #7
     (`olean-replay-cs1-s6` once adopted).
   - `olean-replay-6a-land` is therefore not adoptable.

## Push and PR

- `git push -u origin land/gsw-6a-fills`: new branch at `ccca6f804552f72b400c09e7a3bd694371bdf568` (`ls-remote` confirms).
- **Draft PR #366** into `cryptography/pass-shelat-ch2-4`: https://github.com/Shilun-Allan-Li/tcslib/pull/366
  ("GSW 6a fills: all 98 targets proved (branching programs, Barrington, NAND form, formula arithmetic)"). The body is
  `pr-body.md` in the evidence and ends with "Gate: to be staged (Codex)".

## Evidence

`gsw-6a-fills-final-r1-phase2-evidence.zip` (SHA256SUMS inside), listed in `evidence-SHA256SUMS`. It contains:

- `tools/`: the scripts written for this job, and the attempt-1 controls generator;
- `log/`: the head, the tip, the commit list, signatures and trailers, the range-diff, the LE equality check, the
  deleted trees and the merge-tree against the new tip;
- `repro/`: `mkbase` and the 7-patch reproduction;
- `le/`: the per-edit splits;
- `mergefile/`: the three-way merge inputs and outputs for U3 and U8;
- `order/`, `plan/` and `state/` (`state.json`), `full-order.txt`;
- `build/`: `results.jsonl` and the 564 module logs;
- `checks/`, `snapshot/` (verify outputs), `output-map/`;
- `admissions/`, `decls2/`, `statements/` (`touched`);
- `rule10/`: the seal records and runs, the controls (both attempts), `sealcmp` and the worker comparison;
- `probes/`, `probe-src/`, `scan/`, `lint/`, `dup/`;
- `pr-body.md`.

## Re-replay on snapshot #7

**Verdict: PASS.** The branch was merged up to the records tip twice and re-replayed on olean snapshot #7. All checks equal
the #6 run's, so the merges are pushed and #366's body is updated.

Maintainer sub-agent, 2026-11-17, 19:21–20:35Z. Work directory: `$SP/g6aland7`. Replay tree: `$SP/olean-replay-6a-land7`.
Evidence: `gsw-6a-fills-final-r1-phase2-s7-evidence.zip` (SHA256SUMS inside), listed in `evidence-SHA256SUMS`.

### Merges
The worktree `$SP/wt-6a-land` (sparse) was on `land/gsw-6a-fills` = remote head `ccca6f80`.

| # | Commit | Tree | Content |
|---|---|---|---|
| 20 | `e4d77a5e675f260b8e0be6851e352efa414d5a6a` | `9a1e8d98e7bced09388d17bcb6188c2362b2f116` | signed `--no-ff` merge of the tip `55f553715f280be36827ad86a94c93db39ec56c3`, whose Lean equals snapshot #7's T `a1fa7b65` (#347 + #355). Conflict-free; equal to `git merge-tree` |
| 21 | `93ae671e8f638e86def66dd5ac0a312c8bec4f5c` | `c8ba8961434710a5fda05ff34c8b318226e44cec` | signed `--no-ff` merge of the tip `555f0fe1b10a20d1be72386a97c6fe7a2f39c204`, after #365 (`Pairing/Group.lean` dedup), on the coordinator's update during the build. Conflict-free; equal to `git merge-tree` |

- Both merges have `gpgsig` and end with the two required trailers (`log/merge-msg*.txt`).
- **The branch's own change is unchanged.** `git diff <tip> <head>` is byte-equal to phase 2's `git diff 036d8239 ccca6f80`
  at both steps (SHA-256 of the diff `364f447e…`, 24 files).
  - The Lean diff `a1fa7b65 → e4d77a5e` is byte-equal to phase 2's Lean diff (`58407ffb…`). So `e4d77a5e`'s Lean is
    snapshot #7's Lean plus exactly the 6a changes (#358/#359/#360, the addendum, the fills, LE-gf1..4).
  - The Lean diff `e4d77a5e → 93ae671e` equals `a1fa7b65 → 555f0fe1` (`f666c34f…`): `Group.lean` only.
- `git push origin HEAD:land/gsw-6a-fills`: `ccca6f804..93ae671e8`, fast-forward; `ls-remote` confirms.

### Replay
| Check | Result |
|---|---|
| Snapshot #7 (`5105c514…`; map and files manifest byte-equal to the adoption record's copies) | rehash **0/0/0** at the start, after stage 1, after stage 2, after the probes and at the end |
| Copy | `cp -al $SP/olean-snapshot $SP/olean-replay-6a-land7`; `mloverlay.sh` (3346 symlinks); `mathlibextra.sh` NthRootLemmas `c0a9cff0…` (lean rc 0) |
| Exports | `wtx` = `git archive e4d77a5e`, `wtx2` = `git archive 93ae671e`: 1599 files each, `exportcheck.py` 0/0/0 |
| Plan, stage 1 | `stateplan init` at `a1fa7b65` (1434 modules); `downorder` against the tip: 23 changed, 579 downstream; `fullorder` 1447; **build 564** (551 existing + 13 new), reuse 883. The queue and `down` sets equal phase 2's |
| Build, stage 1 | `tools/run-build-land7.sh` (phase 2's `run-build-land.sh` re-pointed; recipe `runner.py` unmodified, one module per call, slot gate before each, disk gate 1.5 GB). 19:25–20:11Z, 2742 s; no slot waits (at most 1 other `lean` seen); max RSS 4.57 GB |
| Result, stage 1 | `permod`: **564 modules, rc≠0 0, `error:` 0, `error(` 0**, 0 log/record mismatches. Sorry warnings 103, warnings 205 (phase 2: 103, 205). `stateplan update` (564 taken), `check` at `e4d77a5e` over 1447: RESULT OK |
| Plan, stage 2 | `downorder 93ae671e` against `e4d77a5e`: 1 changed (`Group`), 22 downstream; `stateplan plan` at `93ae671e`: **build 22** (= down), reuse 1425 |
| Build, stage 2 | `tools/run-build-land7-s2.sh` (same, with `wtx2`): Pairing/*, KeyExchange/Joux and KeyExchange, IdentityBased/* (BonehBoyen, BonehBoyenMachine/*, BonehBoyenSecurity/*), AdvancedEncryption, root. 20:12–20:14Z, 75 s. **22 modules, rc 0, 0 errors, 0 warnings** |
| State | `stateplan update` (22 taken), then `check` at `93ae671e` over 1447: **RESULT OK** (after the build and again at the end) |
| Links | rebuilt 576 (564 ∪ 22): link count 1; reused 871: snapshot #7's inodes; no `.ilean`, no symlink outside `Mathlib/` |
| Determinism vs the #6 run | 256 of the 564 have the same closure key as in phase 2: **256/256 byte-equal oleans and logs**. Of the 308 whose key changed through Stage 1, 305 have byte-equal oleans; the other 3 are Stage 1's own changed modules (`Cryptography/Games`, `ZeroKnowledge`, `Encryption/PublicKey/Trapdoor`, as phase 2 predicted). All 564 logs are byte-equal, and no warning or sorry count differs (`cmp/build-vs-s6.tsv`) |
| Stage-2 vs #365's replay | the 12 stage-2 modules outside 6a's downstream have oleans byte-equal to `olean-replay-grpfix`'s map (`28677767…`; read only) |
| Output map | Mathlib excluded (`mapnoml.py`): **1478 entries, `11d9fbfd0692b6332e917e84ea318147187d443c34c22a73d40827a913484dc6`**, stable at the end. Against #7: 1454 equal, 11 changed (the 10 of phase 2 plus `Pairing/Group`), 13 added. Against #365's replay: 1455 equal, 10 changed (the 6a-touched owners, the facades, the root), 13 added. The intermediate map at `e4d77a5e` was `4884c248…` |

### Checks at `93ae671e`
- **Admissions** (`sorryscan.py`): 0 in the 13 6a modules. Library: **192 in 44 modules**, identical line by line to snapshot #7's
  scan at `a1fa7b65` (and at `e4d77a5e`). The 22 stage-2 modules have 0 sorry warnings.
- **Axioms:** `AxiomsLand.lean` unchanged; **its log is byte-equal to phase 2's** (rc 0). `axcheck.py` output is byte-equal: 98
  targets OK, 859 census constants, 0 non-standard, 0 TRACE lines, no `sorryAx`; `layerNAND*`, `toNANDForm`, `const_eval`,
  `eval_node_nil` and the six public lemmas standard (`prefixVal_eq_of_false`: `propext` only).
- **Canonical coe-A seals,** 22 owners (`tools/rule10_land7.sh land probes collect coeA`, phase 2's driver re-pointed; same
  prefixes, tools and gating). `touched.json` regenerated against `555f0fe1`; its `files` part and TSV equal phase 2's.
  - `tools/sealcmp7.py`: **22/22 identical to phase 2 in every respect but `rev`** — request sets, all other record fields,
    probe sources, rc, error lines, sealsum rows and whole probe logs. Failures are only the pre-existing Adder 3,
    DAGTransform 11, TreeNCAC 2, Hierarchy 2, TreeDAG 25 (same declarations). 0 new failing declarations.
  - **One difference, explained:** the shared collector's log has one more catalogue line than phase 2's (`CAT-COUNT`
    5965 vs 5964): Stage 1's abbrev `Turing.ModuleHost.hostTMView` (`Complexity/TuringMachine/Build/ModuleHost`). It is
    outside every owner's closure, so no seal changed. The Stage 1 owners are not 6a owners and were not re-sealed here.
- **decls2** (pinned `fa81981a…`) against `555f0fe1`: 289 ADDED, 1 REMOVED, 0 CHANGED; **byte-equal to phase 2's output**
  (and likewise at `e4d77a5e` against `55f55371`).
- **Lint:** `campaign_style_lint --check8b` (Complexity) 25 FAIL / 390 WARN at the tip and the head; the FAIL/WARN delta is
  byte-equal to phase 2's (the 4 shorter check-8 lists). The only lines that differ from phase 2's outputs are INFO size lines
  of Stage 1's files, the same at tip and head. `--check8b TCSlib/Cryptography`: byte-equal tip vs head (92/103). `style_lint`
  on the 23 files: byte-equal to phase 2's at tip and head. No new FAIL or WARN.
- **Not re-run:** paired controls, the explicit-unfold scan, root coe-A, the duplication sweep. Their inputs are unchanged: the 6a
  sources are blob-equal, and the owners' seals and probe logs are byte-equal.

### Housekeeping
- Slots: one Lean process at a time; gate before every module and probe (wait while ≥ 3 host-wide); no wait was needed. Disk:
  free 8.6 GB at the start, at least 7.9 GB throughout.
- `$SP/olean-replay-6a-land` (#6, superseded) was deleted at 20:30Z after a `/proc` scan found no user
  (`log/procscan-6a-land.txt`, `log/deleted-trees.txt`); free disk 7894 → 8406 MB. `olean-replay-grpfix` and
  `$SP/olean-snapshot` were only read.
- The exports `wtx`, `wtx2`, `exp-tip`, `exp-tip2` are not in the zip; they regenerate from their commits.

### Adoption
`$SP/olean-replay-6a-land7` is the snapshot candidate **only at a merge of #366 whose Lean equals `c8ba8961`**:
`git diff --name-only <merge> c8ba8961434710a5fda05ff34c8b318226e44cec -- '*.lean' lean-toolchain lake-manifest.json lakefile.lean`
must be empty. Its checked state is `state/state-after-update-93ae671e.json` (in the zip, gzipped). If #365's replay is adopted
as snapshot #8 first, this tree still matches #8 + 6a (1455 equal to #8's map). At adoption: remove `Mathlib/`, make the map
(must be `11d9fbfd…`), `basecheck` against that state, swap, verify 0/0/0. Any other Lean change landing first means another
re-replay.

## LE-g50 (Gate 50 pre-dispatch sweep; Seyoon: fix now) — 2026-11-17

Filed by the maintainer from the job's returned report; evidence `le-g50-evidence.zip`
(`51151f449278f1bd4921393c86d5c9190eb9b30b4a5c0c4e31eaa9f8d3740893`, inner SHA256SUMS).

- **Commit** `597fb736e545706a058cc212243a13f6dadfeceb` (tree `df05652d512a702fa8e379fe3f16258f0e1d20d5`) on `93ae671e`,
  signed, pushed fast-forward. Proof-only, 3 files, +24/−51 (diff `475e16b7…`).
  - **U1** `Combinators.lean`: `depth_subst_le`, `maxFanin_subst_le` use `maxDepth_le_of_forall`/`maxFaninL_le_of_forall`
    with `List.forall_mem_map` instead of inline list inductions; sketches updated.
  - **U2** `TreeNCAC.lean`: private `maxDepth_map_le`/`maxFaninL_map_le` deleted; `toBinary_maxFanin_le` and
    `toBinary_depth_le` use the public lemmas.
  - **U3** `Barrington.lean`: private `IsFiveCycle.pow_apply_eq_iff` proved from Mathlib's
    `Equiv.Perm.IsCycleOn.pow_apply_eq_pow_apply` via `IsCycle.isCycleOn` (kept: 4 uses); docstring cites them.
  - `depth_neg`/`maxFanin_neg` unchanged (equalities, not instances).
- **Replay** on `olean-replay-6a-land8` (`cp -al` of `-land7`): 16 modules rebuilt, 1429 reused, all rc 0, 0 errors/
  sorry/warnings; state 1447 OK; link count 1; snapshot #8 and the parent rehash 0/0/0; output map
  `963ddeb472f70afe9a5ae8d2a30574d3fde2348efdf20b9a9ab237b31273cf33` (vs parent: exactly the 3 edited modules changed).
- **Checks:** 0 `sorry` in the 13 6a modules; admissions 192 per module; axioms: 98 targets and all checked constants
  standard, no `sorryAx` (census −6 = the deleted privates' constants); coe-A on 22 owners: no new failures,
  **TreeNCAC 2 → 0 errors (G6A-F05 cleared)**, five owners lose exactly the two deleted matchers from their requests;
  root coe-A 14,105 requests, 0 errors; decls2 289/1/0 (unchanged); `touched.py` 5 CHANGED + 2 private REMOVED; lint no
  new FAIL/WARN.
- **Adoption:** at a #366 merge whose Lean equals `df05652d`; `merge-tree` with the tip is clean and Lean-equal.
