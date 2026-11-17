# gsw-6a-fills · checkpoint 1

**Branch head described: `f437e0d0ce2ab0fa3c116042f4261d5c8c8c8c5a`** (`fill/gsw-6a-fills`, local only).

**Base:** `05999162b77c1f0fef64b07427e1a041a31b43d2`, tree `7d551d6f5278fb79febe1b4eeffb4ca4329dc1d3`, reproduced.

**Units at this head:**
- **Proved, with checks 1–12 for their files:** U4 `BarringtonConverse` (C17–C21, 11 targets), U5 `NC1` (C22–C25, 5) and U11 `ModSum` (F9–F10, 4). That is 20 of the 41 targets.
- **In progress:** U7 `NANDLayering` (sub-agent `layer`), and U9 `CarrySave` with U10 `Compare` (sub-agent `fa`). Their outlines and searches are in `evidence/outlines/` and `evidence/subagents/`. Their files are unchanged at this head (identical to the base).
- While this payload was being assembled, `fa` reported all 14 targets of U9 and U10 proved in its worktree (`evidence/subagents/fa/REPORT-fa.md`). They are not integrated at this head. The next checkpoint integrates and checks them.

No statement changed. No scope request is open. No target looks false.

## 1. Base, records tip and commits

- **`tools/mkbase.sh`** (pack verified with `shasum -a 256 -c` in the pack: 13 OK; and in `inputs/`: 6 OK). It printed `BASE 05999162b77c1f0fef64b07427e1a041a31b43d2 tree 7d551d6f5278fb79febe1b4eeffb4ca4329dc1d3` (`evidence/logs/mkbase.log`).
- **The brief's `git merge --no-ff` recipe** gave the same commit and tree (`evidence/logs/merge-recipe.log`). The branch `fill/gsw-6a-fills` starts there.
- **The clone.** It is a separate blobless clone of GitHub (`--filter=blob:none`) with a sparse work tree that leaves out `briefs/` and `dataset/`.
  - `cryptography/pass-shelat-ch2-4`, `land/gsw-6a-statements` (= `73aedcda…`, #359) and `land/gsw-6a-readers` (= `3ea428fd…`, #360) were fetched by name. Neither `land/` branch had moved.
  - The records inputs were read with `git show 7cbd0c93…:<path>`. All four SHA-256 values equal the brief's (`evidence/tools/records/`).
- **Records tip** at this checkpoint: `8c83367204e515af54ce9d0fe2012344094a3909`. `git merge-tree --write-tree HEAD <tip>` exits 0 and is clean, giving tree `4590e6a9…` (`evidence/git-merge-tree-cp1.txt`).

| # | Commit | Unit | File | Signing |
|---|---|---|---|---|
| 1 | `59599399183e3a06350d282abaeb456c890b6613` | U5 | `BranchingPrograms/NC1.lean` | none |
| 2 | `9603797ef994896cf219856dce61f7eac103df20` | U11 | `FormulaArith/ModSum.lean` | none |
| 3 | `f437e0d0ce2ab0fa3c116042f4261d5c8c8c8c5a` | U4 | `BranchingPrograms/BarringtonConverse.lean` | none |

Each commit touches exactly one owned file. All were made with `git -c commit.gpgsign=false`; `COMMITS.tsv` gives author, committer and signing.

## 2. Preflight, cache, pool, who did what

- **Preflight** (`evidence/logs/preflight.log`):
  - `nproc` 4.
  - No cgroup memory limit (v1 `memory.limit_in_bytes` = 9223372036854771712; no v2 files), so the headroom is `MemAvailable` = 16,254,988,288 B = 15.14 GiB (floor 4 GiB): **pass**.
  - Disk: 15,632,936,960 B free = 14.56 GiB on ext4 (floor 12 GiB): **pass**.
  - To reach the floor I first deleted my own earlier job's scratch clone `gsw6a` and its worktrees. That job (`gsw-6a-statements`) is delivered at `d7a9adb5`, and its two local branches are kept as refs in `/home/user/tcslib`. No dependency tree was copied, moved or deduplicated.
- **Cache.**
  - Roots: 65 Mathlib roots from the addendum's command. The pack's `roots.txt` has 66: its extra line, `Std.Sat.CNF`, is a Lean core module shipped with the toolchain, not a Mathlib cache module (`evidence/logs/roots-note.txt`).
  - The archive store held 3,609 archives (183,702,538 B) left by my earlier job in this session on this host (`cache-store.log`).
  - `TAR_OPTIONS=--no-same-owner lake exe cache get <65 roots>` exited 0: "No files to download; Decompressing 2487 file(s)" (`cache-get.log`). A first attempt failed immediately because `lake` was not on the background shell's `PATH` (`cache-get-attempt0-nopath.log`, rc 127; nothing ran).
  - 0 empty oleans.
  - Every present package matches the manifest. `doc-gen4`, `UnicodeBasic`, `BibtexQuery` and `MD4Lean` are ABSENT, and no module of the order imports them (`packages-check.log`, last line `RESULT present_mismatches=0`).
  - The cache probe `import Mathlib.Algebra.BigOperators.Fin` compiles through `scripts/lean_check_tree.sh` (rc 0, `cache-probe.log`).
- **Pool** (`evidence/logs/pool.log`):
  - A counting semaphore of `flock` slot files, shared by all agents (`tools/poollib.py`, `tools/pool_run.py`).
  - Its size is `min(nproc 4, MemAvailable/4 GB = 4) = 4`, run at **3** to leave CPU for the agents' own tooling. A slot is taken only while `MemAvailable ≥ 2.5 GB`. There have been no changes and no shortage.
  - **Peak memory:** 4,019,396 KiB (`Parity`, in the bootstrap). 327 Lean runs so far.
- **Who did what:**
  - **Lead (main session):** setup, bootstrap, U5 and U11, integration of U4, every check and the delivery.
  - **Sub-agent `bp`:** U4 (`evidence/subagents/bp/`, `REPORT-bp.md`).
  - **Sub-agent `layer`:** U7, in progress.
  - **Sub-agent `fa`:** U9 and U10, in progress.
  - Each sub-agent has its own worktree and its own olean tree, with `.lake/packages` symlinked to the lead's. Only the lead ran `lake` and commits.
  - The seeding of the sub-agents' trees is recorded in `evidence/build/seed-check.txt`. `bp` had already edited its file, so the oleans of that file and its two downstream modules were removed from its tree.

## 3. The six files (lines, base → head)

| Unit | File | Base | Head | r3 estimate | Max width |
|---|---|---|---|---|---|
| U4 | `BranchingPrograms/BarringtonConverse.lean` | 304 | 549 (+245) | 250–400 | 100 |
| U5 | `BranchingPrograms/NC1.lean` | 135 | 266 (+131) | 180–320 | 100 |
| U7 | `CircuitComplexity/NANDLayering.lean` | 388 | 388 | 150–300 | 100 |
| U9 | `FormulaArith/CarrySave.lean` | 297 | 297 | 250–400 | 98 |
| U10 | `FormulaArith/Compare.lean` | 238 | 238 | 150–250 | 100 |
| U11 | `FormulaArith/ModSum.lean` | 196 | 444 (+248) | 150–250 | 100 |

(`evidence/sizes/sizes-cp1.txt`)

## 4. Per unit

### U4 `BarringtonConverse` (sub-agent `bp`; integrated unchanged)

**Proved:**
- C17: `Instr.wire_eval`, `Instr.depth_wire_le`, `Instr.maxFanin_wire_le`.
- C18: `wireComp_eval`, `depth_wireComp_le`.
- C19: `compTree_eval`, `depth_compTree_le`, `maxFanin_compTree_le`.
- C20: `toFormula_eval`.
- C21: `depth_toFormula_le`, `maxFanin_toFormula_le`.

**Private helpers** (namespace `BranchingProgram`):
- `maxDepth_le_of_forall`: `∀ c ∈ cs, c.depth ≤ d → TreeCircuit.maxDepth cs ≤ d`.
- `maxFaninL_le_of_forall`: `∀ c ∈ cs, c.maxFanin ≤ d → TreeCircuit.maxFaninL cs ≤ d`.
- `maxFanin_wireComp_le`: fan-in-2 wires give `(wireComp F G i k).maxFanin ≤ 2`.
- `compTree_eval_list`: `(compTree l i j).eval x = decide ((⟨l⟩ : BranchingProgram w n).yield x i = j)`.
- `depth_compTree_list_le`: `(compTree l i j).depth ≤ (Nat.clog 2 w + 2) * Nat.clog 2 l.length + 1`.
- `maxFanin_compTree_list_le`: `(compTree l i j).maxFanin ≤ 2`.

The last three are well-founded on `l.length`, with `compTree`'s own `termination_by`.

**Readers used:**
- From `Defs`: `Instr.eval_eq`, `yield_eq`, `append_instrs`, `length_eq`, and C1's `yield_nil`/`yield_append` (frozen).
- From `Basic`: `eval_lit`, `Lit.eval_eq`, `depth_lit`, `maxFanin_lit`, `eval_node_true_iff`/`_false_iff`, `maxDepth_nil/_cons`, `maxFaninL_nil/_cons`.
- From O1: `balanced_eval`, `depth_balanced_le`, `maxFanin_balanced_le`.
- **U8's F3 readers, frozen, beyond the brief's expectation:** `TreeCircuit.const_eq`, `const_eval`, `depth_const`, `maxFanin_const`, `and2_eq`, `and2_eval`, `depth_and2_le`, `maxFanin_and2_le`. They were used so as not to re-derive published facts about empty and binary gates. The axiom trace therefore names F3 for U4 as well as C1.
- The file's own readers: `wire_eq`, `wireComp_eq`, `toFormula_eq`, `topDepth_eq`, `compTree_nil/_singleton/_cons_cons`.
- Mathlib: `Nat.clog_of_two_le`, `Nat.clog_mono_right`, `Nat.clog_le_iff_le_pow` (this Mathlib has no `Nat.clog_le_of_le_pow`), `Nat.le_pow_clog`, `Finset.length_toList`, `Finset.card_le_univ`, `Fintype.card_fun`.

**Import added:** `import Mathlib.Data.Fintype.BigOperators`, approved by the lead (`evidence/lead/decisions.md`; `evidence/subagents/bp/scope-request/`).
- Reason: reuse `Fintype.card_fun` and `Finset.card_le_univ`, and get the Pi `Fintype` instance, to bound `|F| ≤ w^w`. At the base, the file's import closure has no `Fintype (Fin w → Fin w)` instance.
- It is a root of the fetched cache (`mathlib-roots.txt` l.21), so no new fetch was needed.

**Sketches.** All 11 sketches were refreshed to name the readers and helpers used. The old and new texts are in `evidence/subagents/bp/sketch-refresh.json` and `REPORT-bp.md` §5. In the module docstring, "(targets admitted with `sorry`)" became "(targets proved here)".

### U5 `NC1` (lead)

**Proved:**
- C22: `exists_fiveCycleRecognizes_of_dagCircuit`.
- C23: `Language.InNC.inPBP_five`.
- C24: `Language.InBWBP.inNC_one`.
- C25: `Language.inNC_one_iff_inBWBP`, `Language.inNC_one_iff_inPBP_five`.

**No private helper.** The `n = 0` case goes through the accepting set (`{id}` or `∅`) as in r3 §H8 item 7. The family is defined inline in the proof.

**Readers used:**
- `DAGCircuit.isFaninTwo_iff`, `isWellFormed_iff` (#360), `toTree_eval`, `toTree_depth_le`, `toTree_maxFanin_le`.
- `Language.inTreeNC_iff`, `TreeCircuitFamily.hasFaninTwo_iff`/`isPolySize_iff`/`hasPolylogDepth_iff` (#360), `TreeCircuitFamily.mem_language_iff`.
- `Language.InNC.inTreeNC_one`, `Language.InTreeNC.inNC`, `BoolCircuit.clog_poly_le`, `TreeCircuit.size_succ_le_two_pow`.
- `BranchingProgramFamily.isPermutation_iff`/`isPolyLength_iff`/`mem_language_iff`, `Language.inPBP_iff`/`inBWBP_iff`, `isPermutation_iff`, `length_eq`.
- `fiveCycleRecognizes_iff`, `isFiveCycle_iff`.
- C1's `yield_nil`, and C9 `isFiveCycle_sigma1`, C13 `barrington_recognizes`, C14 `barrington_length_le`, C15 `isPermutation_barrington` (all frozen).
- U4's C20/C21 (`toFormula_eval`, `depth_toFormula_le`, `maxFanin_toFormula_le`).
- Mathlib: `Equiv.Perm.cycleType_one`, `Nat.pow_log_le_self`, `Nat.clog_mono_right`.

**Sketches refreshed:**
- C22: "the reader `DAGCircuit.isWellFormed_iff`, missing at the base and proposed" became "the reader `DAGCircuit.isWellFormed_iff`".
- C23: "(read through readers of `Language.InTreeNC`, `TreeCircuitFamily.HasFaninTwo` and `HasPolylogDepth`, missing at the base and proposed)" became "(read through the readers `Language.inTreeNC_iff`, `TreeCircuitFamily.hasFaninTwo_iff` and `hasPolylogDepth_iff`)". Also added: "and `⇑sigma1 ≠ id` (a five-cycle has `cycleType {5}`: `isFiveCycle_iff`, `Equiv.Perm.cycleType_one`)".
- C24: the constant is now named, `b = (⌈log₂ w⌉ + 2)(a + k) + topDepth w`. "(through the proposed readers of `Language.InTreeNC` and the `TreeCircuitFamily` predicates, missing at the base)" became "(through the readers `Language.inTreeNC_iff`, `TreeCircuitFamily.hasFaninTwo_iff`, `isPolySize_iff` and `hasPolylogDepth_iff`)".
- Module docstring: "(targets admitted with `sorry`)" became ", proved in the fill phase (gsw-6a-fills)".

No import was added.

### U11 `ModSum` (lead)

**Proved:**
- F9: `modSumInterval_eval`.
- F10: `depth_modSumInterval_le`, `modSumDepth_le`, `maxFanin_modSumInterval_le`.

**Private helpers** (namespace `BoolCircuit.FormulaArith`):
- `maxDepth_le_of_forall` and `maxFaninL_le_of_forall`, the Addendum A family, as in U4.
- `prefixVal_testBit`: `prefixVal c.testBit p = c % 2 ^ p`.
- `val_maskedConst`: `a < 2 ^ p → val x (maskedConst i a p) = (x i).toNat * a`.
- `prefixVal_eq_of_lt_two_pow`: `w ≤ m → prefixVal f m < 2 ^ w → prefixVal f m = prefixVal f w`.
- `val_take_of_lt`: `val x U < 2 ^ w → val x (U.take w) = val x U`.

**Readers used:**
- From CarrySave and Compare, which are foreign and whose targets U9/U10 are still admitted at this head (proved-modulo): `val_eq`, `maskedConst_eq`, `modSumInterval_eq`, `modSumDepth_eq`, `csaReduce_val`, `depth_csaReduce_le`, `maxFaninL_csaReduce_le`, `csaLevels_le`, `geConst_eval`, `depth_geConst_le`, `maxFanin_geConst_le`.
- From U8 (frozen): `const_eval`, `depth_const`, `maxFanin_const`, `and2_eval`, `depth_and2_le`, `maxFanin_and2_le`, `neg_eval`, `depth_neg`, `maxFanin_neg`. From O1: `balanced_eval`, `depth_balanced_le`, `maxFanin_balanced_le`.
- From `Basic`: `eval_lit`, `Lit.eval_eq`, `depth_lit`, `maxFanin_lit`, `eval_node_false_iff`, `maxDepth_nil/_cons`, `maxFaninL_nil/_cons`, `depth_le_maxDepth`, `maxFanin_le_maxFaninL`.
- From `Adder`: `bitsVal_eq_prefixVal`, `prefixVal_zero`, `prefixVal_succ`, `prefixVal_congr`.
- Core: `Nat.mod_pow_succ`, `Nat.toNat_testBit`, `Nat.zero_testBit`. Mathlib: `List.sum_ofFn`, `Finset.sum_le_sum`, `Nat.le_pow_clog`, `Nat.clog_mono_right`, `Nat.div_eq_of_lt_le`, `Nat.div_lt_iff_lt_mul`.

**Imports added:** `import Mathlib.Algebra.BigOperators.Fin` (for `List.sum_ofFn`) and `import Mathlib.Algebra.Order.BigOperators.Group.Finset` (for `Finset.sum_le_sum`). Both are roots of the fetched cache (l.1 and l.4).

**Sketches refreshed:**
- F9:
  - (1) "(`maskedConst_eq`, `eval_lit`, `const_eval`, `val_eq` and `bitsVal` against `Nat.testBit`, …)" became "(`val_maskedConst`: `maskedConst_eq`, `eval_lit`, `Lit.eval_eq`, `const_eval`, `val_eq`, `bitsVal_eq_prefixVal` and `prefixVal_testBit`, …)".
  - (3) "`S < max M 1 · q ≤ 2 ^ w`" became "`S ≤ M (q - 1) < 2 ^ w`, … (`val_take_of_lt`)".
- F10 depth: "depth of a literal `0` (reader missing, see the census)" became "`depth_lit`", and "(`List.take` is a sublist; `depth_le_maxDepth`)" became "(`List.mem_of_mem_take`, `depth_le_maxDepth`, `maxDepth_le_of_forall`)".
- F10 fan-in: "(literal, reader missing; `maxFanin_const`)" became "(`maxFanin_lit`, `maxFanin_const`)".
- The paragraphs were re-wrapped to width 100 (`tools/reflow_sketch.py`).
- F9's `lo ≤ hi` (G6A-F09) stays and is unused, as the brief says.

## 5. Statement changes

None.

## 6. Checks at this head (for U4, U5, U11; the other files are base-identical)

1. **Bootstrap and sweep.**
   - The bootstrap of `order.txt` at the base: 218/218 rc 0, 0 errors in both forms. Exactly the 115 `sorry` declarations of `base-sorries.txt` in 18 modules, matched name by name (`evidence/build/bootstrap/`).
   - Every source equals `SOURCE-SHA256SUMS` (218/218, `source-binding.txt`).
   - **Sweep at the head** over the 9 DOWN modules: 9/9 rc 0, 0 errors, each source bound to `git show HEAD` (`evidence/build/sweep-cp1/summary.txt`).
   - The changed modules' oleans were rebuilt before the sweep: `BarringtonConverse`, `NC1` and `BranchingPrograms` by `evidence/lead/u4-integration/`, and `ModSum` by its own checks.
2. **Admissions:** 95 declarations in 15 modules, 0 mismatches. That is `base-sorries.txt` minus the 20 proved targets (`evidence/admissions/admissions-cp1.txt`). There is no `sorry` token in U4, U5 or U11. The remaining admissions in owned files are U7's 7, U9's 7 and U10's 7 targets.
3. **Statements:**
   - `decls2.py` over the six files: 0 ADDED, 0 CHANGED, 0 REMOVED (empty output, `evidence/stmt/decls2-cp1.txt`).
   - `StmtDump`: the 41 targets at the base and at the head are byte-identical (`StmtDump-base.log`, `StmtDump-head-cp1.log`).
   - **Frozen check** (`evidence/headers/frozen_owned.py`): 6 files PASS with 0 differences against `allow.tsv`, which lists the two admission sentences and the three imports.
   - Controls (`frozen-cp1.txt`):
     - header, prose spill, definition body, reader and unpermitted import each FAIL with 1 difference;
     - a deleted target FAILs with 2 (the missing target and its hunk);
     - `NC1` has no definition or reader, so those two controls are N/A there.
   - The unchanged files PASS (`frozen-base-vs-base.txt`).
4. **Axioms** (`evidence/axioms/AxiomProbe-cp1.log`, `trace-check-cp1.txt`):
   - The census covers 187 stored constants of the six modules. The axioms are `propext`, `Classical.choice`, `Quot.sound` and `sorryAx` only.
   - **U4:** `sorryAx` only through C1 (`yield_nil`, `yield_append`) and U8's F3 (`const_eval`, `depth_const`, `maxFanin_const`, `and2_eval`, `depth_and2_le`, `maxFanin_and2_le`).
   - **U5:** only through C1, C9 (`isFiveCycle_sigma1`), C13–C15 and F3, through U4.
   - **U11:** through U8's F1–F3 and, at this checkpoint, through U9's and U10's targets. Those are this job's units, still admitted (proved-modulo); they leave at the final.
   - U7, U9 and U10's own constants still trace to their own targets, as expected while they are open. `layerNAND` traces to N12–N13 at this head (G6A-F14; `layer` has proved them in its worktree).
5. **Rule 10.**
   - **Seals** A, B, coe-A and coe-B, with `-DmaxErrors=0`, of U4, U5 and U11 at head and base: every probe rc 0, 0 errors, install and EOF records present (`evidence/rule10/cp1-head`, `cp1-base`, `seal-*.tsv`).

     | Owner | Requests at head | At base | #359 reference |
     |---|---|---|---|
     | `BarringtonConverse` | 243 | 243 | 243 |
     | `NC1` | 336 | 333 | 333 |
     | `ModSum` | 273 | 273 | 273 |

     NC1's three extra requests at the head are the `match_1_1` matchers of U4's well-founded private helpers, now in NC1's closure.
   - **No failing declaration.**
   - **Liveness pairs** (`evidence/rule10/live-cp1/summary.txt`): each control is appended to the owner's own full seal probe, so it runs in a consumer's context.
     - U4 reads `BranchingProgram.yield` by `rfl`, against `yield_eq`.
     - U5 reads `DAGCircuit.IsWellFormed` by `Iff.rfl`, against `isWellFormed_iff`.
     - U11 reads `FormulaArith.val` by `rfl`, against `val_eq`.
     - The unsealed negatives were pretested first: 0 errors. Sealed, each negative has exactly 1 error and each positive 0.
     - A `ALL_OK True`, coe-A `ALL_OK True`.
   - **Explicit-unfold scan:** 0 foreign (`cp1-head/explicit-unfold-scan.txt`).
6. **Frozen files:** `git diff --stat 05999162` lists only the three changed owned files (`evidence/git-diff-stat-cp1.txt`).
7. **Lint:**
   - `style_lint`: 0 findings in the six files.
   - `campaign_style_lint TCSlib/Complexity --check8b`: 25 FAIL / 390 WARN over 513 files at both base and head, with identical line sets (`evidence/lint/`).
8. **Sizes:** §3; no line over 100, no file over 1000.
9. **Docstrings:** 12 private helpers, 0 without a formula or "Glue."; 9 proofs of 20 lines or more, 0 without a sketch (`evidence/docs/hygiene-cp1.txt`).
10. **Clash and shadow:**
    - 12 new names, all private, 0 clashes with `TCSlib/` or `audits/` at the base, and none contains `NAnd` or `toLayered`.
    - No new short name exists elsewhere, so no unqualified use can change resolution (`evidence/clash/clash-cp1.txt`).
11. **Reuse and overlap:** §7.
12. **Reproduction:**
    - `git am` of `patches/` at the base, in a scratch clone with `COMMITS.tsv`'s committer data, reproduces all 3 hashes (`evidence/reproduce-cp1.log`).
    - The scratch clone is a shared, sparse partial clone like the work clone.
    - `src/` equals the head's six files byte for byte.

## 7. Overlap and reuse

- **The list-bound family** `maxDepth_le_of_forall` / `maxFaninL_le_of_forall` is private in U4 and U11, and `fa` writes it in U9/U10 under the same names and forms (Addendum A, `SUBAGENT-COMMON.md`).
  - `Basic.lean` publishes only the member-to-max direction (`depth_le_maxDepth:265`, `maxFanin_le_maxFaninL:273`).
  - The converses exist only as other files' private lemmas (`TreeNCAC.lean:215,226`, `TreeDAG.lean:407,420`, of different forms), which were not copied.
  - **Promotion request P1** to `Basic.lean`; until then this is disclosed duplicated material, of the same family across the job's files.
- **`prefixVal_testBit`** is private in U11, and `fa` plans the same lemma in U10 for `constBits`.
  - Neither TCSlib nor Mathlib has it. Core's `Nat.mod_two_pow_succ` (`Init/Data/BitVec/Bitblast.lean:163`) is private.
  - `LupanovGates.testBit_ofBits` has no bridge to `bitsVal`.
  - Searches: `evidence/lead/searches.md` and `evidence/subagents/fa/progress.md` (BITS-LEMMA).
  - **Promotion request P2** to `Adder.lean`.
- **`prefixVal_eq_of_lt_two_pow` and `val_take_of_lt`** are new facts about `Adder.prefixVal` and `FormulaArith.val`, with no relative found (`searches.md`). They are promotion candidates for `Adder.lean`/`CarrySave.lean` (P3).
- **U5's inline facts:**
  - "`⇑sigma1 ≠ id`" is derived from `isFiveCycle_iff` and `Equiv.Perm.cycleType_one`. No lemma `IsFiveCycle.ne_one` exists in TCSlib.
  - The polynomial bound `4^(b(log n+1)) ≤ 4^b (n+1)^(2b)` is a calc step. NCAC's `inTreeNC_one` has an analogous inline bound; there is no lemma to reuse.
- **U4:** see `evidence/subagents/bp/searches.md`.

## 8. Promotion and scope requests

- **Promotion requests:**
  - P1: `TreeCircuit.maxDepth_le_of_forall` and `TreeCircuit.maxFaninL_le_of_forall` to `Basic.lean`.
  - P2: `prefixVal_testBit` to `Adder.lean`.
  - P3: `prefixVal_eq_of_lt_two_pow` and a `val_take` lemma to `Adder.lean`/`CarrySave.lean`.
- **Scope requests:** none. Only the one import request inside the job, approved by the lead because it is within the brief's *Imports* rule.

## 9. Questions for Seyoon

None at this checkpoint.

## 10. Evidence

`evidence/` with its manifest `evidence/SHA256SUMS`, and the top-level `SHA256SUMS`. The main locations:
- `logs/`: preflight, cache, packages, pool.
- `build/`: the bootstrap, seeds, base DOWN rebuild and head sweep.
- Checks: `admissions/`, `stmt/`, `headers/`, `axioms/`, `rule10/` (seals, probe sources, liveness), `lint/`, `sizes/`, `docs/`, `clash/`.
- Work records: `outlines/` (U7, U9, U10), `lead/` (logs, searches, decisions), `subagents/` (a copy at checkpoint time; `fa` and `layer` are still writing).
- `tools/`: this job's tools and the statement job's adapted ones, with each change in the tool's header.
- `git-merge-tree-cp1.txt` and `reproduce-cp1.log`.
