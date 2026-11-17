The **GSW phase 6a fills**: all **98** 6a targets are proved. That is 97 admitted targets proved by the fills, plus `const_eval`, which LE-g45 already proved. They cover branching programs, both directions of Barrington's theorem, the NC¹ corollary, the DAG-to-NAND conversion and its layering, and formula arithmetic. The work is the in-house units U1–U3, U8 and U6 and the external `gsw-6a-fills` delivery (U4, U5, U7, U9, U10, U11), with the four ruled landing edits and the Gate 50 sweep's LE-g50. Every 6a file has **0 `sorry`**.

**Stacks #358, #359 and #360 and contains them.** The branch started at the records tip `036d8239` (Lean-equal to olean snapshot #6, T `8060f6b7`). It merges #358 (`a616adca`), #359 (`d154c883`, with LE-g45/LE-g45b) and #360 (`cc05f76c`) as signed `--no-ff` merges, and then adds 16 commits. Merging #358, #359 and #360 first shrinks this diff to those 16 commits; GitHub then shows only the fills and the landing edits.

**Head:** `597fb736e545706a058cc212243a13f6dadfeceb` (tree `df05652d512a702fa8e379fe3f16258f0e1d20d5`). It is the 6a head `ccca6f80`, plus two signed `--no-ff` merges of the records tip (see "Up to date with the tip" below), plus the signed landing edit **LE-g50** (see "LE-g50" below). All 22 commits on the first-parent line are signed (`gpgsig`). The new 6a files are under `Complexity/`.

## Up to date with the tip (2026-11-17)
- `e4d77a5e675f260b8e0be6851e352efa414d5a6a` (tree `9a1e8d98e7bced09388d17bcb6188c2362b2f116`): signed `--no-ff` merge of the tip `55f553715f280be36827ad86a94c93db39ec56c3`, whose Lean equals olean snapshot #7's T `a1fa7b65` (#347 + #355: cleanup Stage 1 and DW-5). Conflict-free.
- `93ae671e8f638e86def66dd5ac0a312c8bec4f5c` (tree `c8ba8961434710a5fda05ff34c8b318226e44cec`): signed `--no-ff` merge of the tip `555f0fe1b10a20d1be72386a97c6fe7a2f39c204`, after #365 (Pairing `Group.lean` dedup). Conflict-free.
- **The branch's own change is unchanged.** `git diff <tip> <head>` is byte-equal to the earlier `git diff 036d8239 ccca6f80` (24 files: the 23 `.lean` files and `machine-library-design.md`). The head's Lean is snapshot #7's Lean, plus #365's `Group.lean`, plus exactly the 6a changes (#358/#359/#360, the addendum, the fills and LE-gf1..4).

## Commits by unit
1. Merges: `49f88fef` #358, `76efe1ba` #359, `32ec2ef5` #360.
2. **#360 addendum 2 (LE-gf3, part 1)**, `40c7215c`: four public lemmas, promoted from the fills' private copies (statements and proofs are the worker's, verbatim). Each docstring has the formula and "Glue.". The names are clash-free in TCSlib, audits, Mathlib, Batteries and core.
   - `Basic.lean`: `TreeCircuit.maxDepth_le_of_forall`, `TreeCircuit.maxFaninL_le_of_forall`.
   - `Adder.lean`: `prefixVal_eq_of_false`, `prefixVal_testBit`.
3. **In-house units**, landed as content commits, not merges (the in-house branches' merges of #359/#360 are not carried):
   - `c7fb15ee` **U1/U2**: `Defs` and `Eval` (C1–C8, 16 declarations), with the blobs of `fill/gsw-6a-u1-u2` `f31382a5`.
   - `bec8eefd` **U3**: `Barrington` (C9–C16, 11). The in-house diff is applied by a three-way merge onto #359's file, so LE-g45/45b's docstrings are kept. The merge is clean and line-for-line equal to the in-house diff.
   - `2ddada22` **U8**: `Combinators` (F1–F3, 23), from `fill/gsw-6a-u8-u6` `b65668a9` by a three-way merge onto #359. The one conflict was `const_eval`'s body, and **LE-g45's proof** (from `eval_node_nil`) was kept. Every other line of the in-house diff applies unchanged.
   - `e0d3e537` **U6**: `NANDForm` (N1–N6, 6), with the blob of `b65668a9`.
4. **External units** (exchange `60703442`, worker head `bb7efa82` on base `05999162`), cherry-picked with `-S`. The worker's messages and authorship are kept unchanged. Its own session trailers were kept and no maintainer trailer was added. `git range-diff 05999162..bb7efa82` against these 7 commits is **7/7 `=`**. The 7 patches reproduce `bb7efa82` hash for hash on `mkbase.sh`'s base.
   - U4 `e2b7020c` (C17–C21) and `2f38e2b9` (helper sketch), `BarringtonConverse`;
   - U5 `80de2e4e`, `NC1` (C22–C25);
   - U9 `72bfcab0`, `CarrySave` (F5–F6);
   - U10 `1bf78b47`, `Compare` (F7–F8);
   - U11 `153811f1`, `ModSum` (F9–F10);
   - U7 `bf8aef14`, `NANDLayering` (N7–N13).
5. **Landing edits**, as separate signed commits. They are the recorded `landing-edits-proposed.diff` (SHA-256 `01c07a11…`) verbatim; the 8 edited files equal `bb7efa82` with that diff applied.
   - `91e2f807` **LE-gf1** (GF-F01, ruling GF-W4 A). C23/C24 use Mathlib's `Nat.pow_log_le_add_one` instead of re-deriving it (+5/−8).
   - `c1a444f2` **LE-gf3, part 2** (GF-F02, ruling GF-W1 A). It deletes the 14 private copies (BarringtonConverse 2, CarrySave 3, Compare 6, ModSum 3) and makes CarrySave's `depth_getD_le`/`maxFanin_getD_le` public. The uses are qualified (+36/−168).
   - `22636300` **LE-gf2** (GF-F04, ruling GF-W2 A, Seyoon's freeze exception). One sentence of the frozen `layerNAND` docstring is updated (+3/−2).
   - `ccca6f80` **LE-gf4** (GF-F03, ruling GF-W5 A). F9 uses `Finset.sum_le_card_nsmul` (+6/−6). **It compiles, so it is kept.**
6. Tip merges: `e4d77a5e` and `93ae671e` (above).
7. `597fb736` **LE-g50** (Gate 50 sweep U1–U3; below).

## Rulings applied (2026-11-17)
- GF-W1: repaid at landing by LE-gf3, with no ledger row.
- GF-W2: LE-gf2.
- GF-W3: `NANDLayering` is accepted at 947 lines. It is 948 after LE-gf2's rewrap, still under 1,000.
- GF-W4/W5: LE-gf1 and LE-gf4.

## LE-g50 (Gate 50 sweep, 2026-11-17)
**Why.** Gate 50's pre-dispatch sweep stopped staging on three unledgered duplicates in our own code. The phase-1 review had noted U1/U2 but never filed them. Seyoon ruled **fix now in #366**, as a proof-only landing edit, followed by a short re-replay.

**What.** `597fb736e545706a058cc212243a13f6dadfeceb` (+24/−51, 3 files). It is proof-only: no statement, header or docstring statement changes.
- **U1, `FormulaArith/Combinators`:** `TreeCircuit.depth_subst_le` and `maxFanin_subst_le` dropped their inline list inductions. They now use the public `TreeCircuit.maxDepth_le_of_forall` / `maxFaninL_le_of_forall` (this PR's #360 addendum), together with `depth_le_maxDepth` / `maxFanin_le_maxFaninL` and `List.forall_mem_map`. The proof sketches are updated.
- **U2, `TreeNCAC`:** the private `maxDepth_map_le` / `maxFaninL_map_le` are deleted. They were the `cs.map f` case of the same public lemmas. Their two uses (`toBinary_maxFanin_le`, `toBinary_depth_le`) now call the public lemmas through `List.forall_mem_map`. These privates were TreeNCAC's two pre-existing coe-A failures (G6A-F05), which are now **cleared**.
- **U3, `BranchingPrograms/Barrington`:** the private `IsFiveCycle.pow_apply_eq_iff` is now the `s = Finset.univ` case of Mathlib's `Equiv.Perm.IsCycleOn.pow_apply_eq_pow_apply`, via `Equiv.Perm.IsCycle.isCycleOn` and the full support (`IsFiveCycle.apply_ne`), and its docstring cites the Mathlib lemma. It is kept rather than inlined: it has four uses in `conjugator_conj` and a 5-line body.
- Not changed: `depth_neg` / `maxFanin_neg` keep their equality form. They are not instances of the `_le_of_forall` lemmas.

**Re-replay.** Never with `lake build`; one Lean process at a time, slot-gated and disk-gated.
- **Tree:** `olean-replay-6a-land8` = `cp -al` of `olean-replay-6a-land7` (this PR at `93ae671e`; map `11d9fbfd…`).
- **Build:** the downstream of the 3 files, **16 modules** in dependency order: the 3 files, the BranchingPrograms/FormulaArith/CircuitComplexity facades, BarringtonConverse, NC1, CarrySave, Compare, ModSum, Hierarchy, NCAC, Parity, ComputationalModels and the root. Result: **rc 0, 0 errors, 0 warnings, 0 sorry**. 1,429 modules were reused.
- **State check** at `597fb736` over the 1,447-module order: **RESULT OK**, after the build and at the end.
- **Links:** the 16 rebuilt oleans have link count 1, and the reused ones are the parent tree's inodes.
- **Rehash:** the parent tree (`11d9fbfd…`) and olean snapshot #8 (map `28677767…`) both rehash **0/0/0** at the start, after the build and at the end.
- **Output map** (Mathlib excluded): 1,478 entries, **SHA-256 `963ddeb472f70afe9a5ae8d2a30574d3fde2348efdf20b9a9ab237b31273cf33`**, stable at the end. Against the parent: 1,475 equal and 3 changed (the 3 edited modules). The 13 rebuilt downstream modules are byte-equal to the parent's. Against snapshot #8: 1,455 equal, 10 changed, 13 added, the same sets as before LE-g50.

**Checks at `597fb736`:**
- **Admissions:** **0 `sorry`** in the 13 6a modules. Library: **192 in 44 modules**, equal module by module to the `93ae671e` scan.
- **Axioms:** the same probe, rc 0. All **98 targets** are standard. `layerNAND*`, `toNANDForm`, `const_eval`, `eval_node_nil` and the six public lemmas are standard as well. There are **0 TRACE lines**, 0 non-standard axioms and no `sorryAx`. The census has 853 constants instead of 859; the 6 removed are exactly the deleted privates and their auxiliaries (`maxDepth_map_le`/`maxFaninL_map_le`, `._proof_1_3`, `.match_1_1`).
- **Canonical coe-A, 22 owners**, compared with the #7 re-replay records:
  - 14 owners are identical in every respect but `rev`.
  - Barrington and Combinators: same request sets, 0 errors, byte-equal probe logs. Only the source hash, the probe hash and the probe's insertion lines changed.
  - **TreeNCAC: 218 requests, 2 → 0 errors.**
  - BranchingPrograms (337), NC1 (335), CircuitComplexity (3,736), Hierarchy (353) and ComputationalModels (1,104) each lose exactly the two deleted `*_map_le.match_1_1` matchers. Their rc, error lines and failing declarations are unchanged.
  - Remaining failures are the pre-existing Adder 3, DAGTransform 11, Hierarchy 2 and TreeDAG 25, on the same declarations. **0 new failures.**
- **Root coe-A** (its requests change too): **14,105 requests, rc 0, 0 errors**. Against the #6 run's 14,098, the request set differs by −2 for the LE-g50 matchers, plus the tip's Stage 1/#365 changes.
- **decls2** against the tip `cd8b4765` (Lean-equal to `555f0fe1`): **289 ADDED, 1 REMOVED, 0 CHANGED**, equal to the earlier output up to line numbers. **touched.py** (private declarations included) `93ae671e → 597fb736`: 5 CHANGED (`depth_subst_le`, `maxFanin_subst_le`, `toBinary_maxFanin_le`, `toBinary_depth_le`, private `IsFiveCycle.pow_apply_eq_iff`) and 2 REMOVED (the TreeNCAC privates). Against the tip, the only change is those two privates moving from UNCHANGED to REMOVED.
- **Lint:**
  - `campaign_style_lint --check8b` gives 25 FAIL / 390 WARN. The FAIL/WARN lines are byte-equal to `93ae671e`'s; only INFO size lines changed (Combinators 768 → 762, TreeNCAC 382 → 361).
  - `Cryptography` is byte-equal.
  - `style_lint` on the changed files is byte-equal.
  - No added line is over 100 characters.

## Re-replay on olean snapshot #7 (at `93ae671e`)
Never with `lake build`; one Lean process at a time, slot-gated (at most 3 on the host) and disk-gated (1.5 GB). Record: "Re-replay on snapshot #7" in `briefs/lattice-gsw/phase6/fills-final-r1/phase2.md`.
- **Tree:** `olean-replay-6a-land7`, a `cp -al` copy of snapshot #7 (map `5105c514…`), with the Mathlib overlay (3346 symlinks, NthRootLemmas `c0a9cff0…`).
- **Stage 1, at `e4d77a5e`:** the whole downstream of the 23 changed files, **564 modules** (551 existing, 13 new; the same set as on #6). **rc 0, 0 `error:`/`error(`** for all 564; 103 sorry warnings and 205 warnings, as on #6. State check at `e4d77a5e` over the 1,447-module order: RESULT OK.
- **Stage 2, at `93ae671e`:** `Group.lean`'s downstream, **22 modules** (Pairing/*, KeyExchange/Joux, IdentityBased/*, AdvancedEncryption, root). **rc 0, 0 errors, 0 warnings.** State check at `93ae671e` over 1,447 modules: **RESULT OK**.
- **Links:** all 576 rebuilt oleans have link count 1; the 871 reused ones are snapshot #7's inodes. Snapshot #7 rehash: **0/0/0** at start, after each stage and at the end.
- **Determinism:** 256 of the 564 stage-1 modules have the same closure key as in the #6 run; all 256 have byte-equal oleans and logs. Of the 308 whose key changed through Stage 1's files, 305 have byte-equal oleans too; the other 3 are Stage 1's own changed modules (`Games`, `ZeroKnowledge`, `Trapdoor`). Logs: 564/564 byte-equal. The 12 stage-2 modules outside 6a's downstream are byte-equal to #365's replay (`olean-replay-grpfix`).
- **Output map** (Mathlib excluded): 1,478 entries, **SHA-256 `11d9fbfd0692b6332e917e84ea318147187d443c34c22a73d40827a913484dc6`**. Against #365's replay map (`28677767…`): 1,455 equal, 10 changed (the 6a-touched owners, the facades and the root), 13 added.

## Checks at `93ae671e`
- **Admissions:** **0 `sorry`** in all 13 6a modules (0 warnings of any kind). Library-wide: **192 in 44 modules, equal to snapshot #7 module by module**.
- **Axioms:** the probe source and its log are byte-equal to the #6 run's. All 98 targets: `propext`/`Classical.choice`/`Quot.sound` only. Census of the 13 modules and TreeNCAC: 859 constants, 0 non-standard, **0 `sorryAx` traces**. `layerNAND`, `layerNAND_gates`, `layerNAND_output`, `toNANDForm`, `const_eval`, `eval_node_nil` and the six new public lemmas: standard only (`prefixVal_eq_of_false`: `propext` only).
- **Canonical coe-A** on the 22 changed owners: **22/22 identical to the #6 run** in request sets, every record field except `rev`, probe sources, rc, error lines and whole probe logs. Every 6a owner has 0 errors. The failures are only the pre-existing ones: Adder 3, DAGTransform 11, TreeNCAC 2, Hierarchy 2, TreeDAG 25. **0 new failures.** The shared collector's catalogue has one more entry than on #6 (Stage 1's abbrev `Turing.ModuleHost.hostTMView`), which is outside every owner's closure.
- **decls2** against the tip: **289 ADDED, 1 REMOVED, 0 CHANGED**, byte-equal to the #6 run's output. ADDED = #358/#359 (268) + #360 (15) + the 6 public lemmas; the REMOVED entry is `eval_node_nil` leaving `Hierarchy` (LE-g45's move). decls2 strips comments, so LE-gf2 does not show as CHANGED.
- **Lint:** `campaign_style_lint --check8b` gives 25 FAIL / 390 WARN at both tip and head. The FAIL/WARN delta is byte-equal to the #6 run's: only shorter check-8 lists from #360's readers. `Cryptography` is unchanged between tip and head. `style_lint` on the changed files: byte-equal to the #6 run's, at tip and head.
- **Not re-run on #7**, because their inputs are unchanged: the paired controls (ALL_OK on #6), the explicit-unfold scan (0 new foreign on #6), root coe-A (14,098 requests, 0 errors on #6) and the duplication sweep. The 6a sources are blob-equal to the #6 run's, and the owners' seals and probe logs are byte-equal.
- **Duplication sweep (on #6):** the 6 public lemmas and the 75 remaining private helpers in the 6a files were searched by name in TCSlib, audits, Mathlib, Batteries and core, and by body. No duplicate was found.

## Disclosed
- In-house frozen docstrings are now stale. They are left as frozen, for a docstring follow-up like LE-g45b:
  - `Defs:32`, `Eval:35`, `Barrington:32` say "targets admitted with `sorry`";
  - `NANDForm:61` and `:455` say "While N2 is admitted, `sorryAx` reaches `toNANDForm`".
- `NANDLayering` is 948 lines (GF-W3 accepted 947; LE-gf2 rewraps one line).
- LE-gf3's size: the review's summary said +68/−154, but the recorded diff applies as +72/−168 (addendum +36, part 2 +36/−168).
- The in-house units had no external review before this PR. Their phase-2 checks are the ones above.
- **Adoption:** `olean-replay-6a-land8` is the snapshot candidate only at a merge of this PR whose Lean equals the head tree `df05652d`: `git diff --name-only <merge> df05652d512a702fa8e379fe3f16258f0e1d20d5 -- '*.lean' lean-toolchain lake-manifest.json lakefile.lean` must be empty. The tip's Lean is snapshot #8's (#7 + #365), which this PR already contains; `git merge-tree` with the tip `cd8b4765` is clean and has exactly this Lean. Any other Lean change landing first means another re-replay. `olean-replay-6a-land7` (at `93ae671e`) is superseded but kept as the parent; the old `olean-replay-6a-land` (on #6) was deleted.

Gate: to be staged (Codex)

🤖 Generated with [Claude Code](https://claude.com/claude-code)

https://claude.ai/code/session_01PqpVTiuDcjSqhyfbqnsVxA
