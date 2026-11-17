# gsw-6a-fills · final

**Branch head described: `bb7efa82af89141535e7a4adc49c6d97aef85de8`** (`fill/gsw-6a-fills`, local only).

**Base:** `05999162b77c1f0fef64b07427e1a041a31b43d2`, tree `7d551d6f5278fb79febe1b4eeffb4ca4329dc1d3`.

**All 41 targets of the six units are proved:**
- U4 `BarringtonConverse` (C17–C21, 11), U5 `NC1` (C22–C25, 5), U7 `NANDLayering` (N7–N13, 7);
- U9 `CarrySave` (F5–F6, 7), U10 `Compare` (F7–F8, 7), U11 `ModSum` (F9–F10, 4).

There is no `sorry` in any owned file. No statement changed. No scope request is open. No target looked false.

Every check passes:
- the 9-module sweep (rc 0, 0 errors, every source bound to `git show HEAD`);
- admissions: **74 declarations in 12 modules**, 0 mismatches;
- decls2: 0 ADDED, 0 CHANGED, 0 REMOVED;
- StmtDump identical at base and head;
- frozen check PASS, with every control failing as stated;
- axioms: `sorryAx` only through in-house frozen targets, and G6A-F14 met;
- seals A, B, coe-A, coe-B of the six owners at head and base: 0 errors, no failing declaration;
- liveness `ALL_OK True` (A and coe-A); explicit-unfold scan 0 foreign;
- lint: 25 FAIL / 390 WARN over 513 files at both base and head, with identical line sets;
- `git am` reproduces all 7 hashes.

Three questions for Seyoon are in §9: GF-W1 (duplicated private helpers), GF-W2 (a stale frozen docstring) and GF-W3 (the size of `NANDLayering`).

Checkpoint 1 (head `f437e0d0`) was delivered as exchange commit `ae630297`.

## 1. Base, records tip, commits

- **Pack verification.** `shasum -a 256 -c` gave 13 OK in the pack and 6 OK in `inputs/`.
- **`tools/mkbase.sh`** printed `BASE 05999162b77c1f0fef64b07427e1a041a31b43d2 tree 7d551d6f5278fb79febe1b4eeffb4ca4329dc1d3` (`evidence/logs/mkbase.log`). The brief's `git merge --no-ff` recipe gave the same commit (`merge-recipe.log`), and the branch starts there.
- **The clone.** It is separate: a blobless clone of GitHub, with a sparse work tree that leaves out `briefs/` and `dataset/`.
  - `cryptography/pass-shelat-ch2-4`, `land/gsw-6a-statements` (= `73aedcda…`) and `land/gsw-6a-readers` (= `3ea428fd…`) were fetched by name. They had not moved.
  - The records inputs were read from `7cbd0c93…`, and their SHA-256 values equal the brief's (`evidence/tools/records/`).
- **Records tip at delivery:** `8c83367204e515af54ce9d0fe2012344094a3909`. `git merge-tree --write-tree HEAD <tip>` is clean (rc 0, tree `2fe59876…`, `evidence/git-merge-tree-final.txt`).
- I heard of no Gate 45 change, and the base was not changed.

| # | Commit | Unit | File | By |
|---|---|---|---|---|
| 1 | `59599399183e3a06350d282abaeb456c890b6613` | U5 | `BranchingPrograms/NC1.lean` | lead |
| 2 | `9603797ef994896cf219856dce61f7eac103df20` | U11 | `FormulaArith/ModSum.lean` | lead |
| 3 | `f437e0d0ce2ab0fa3c116042f4261d5c8c8c8c5a` | U4 | `BranchingPrograms/BarringtonConverse.lean` | `bp` |
| 4 | `9edc2be027fab222c6ca30dbec0759e8f07c3da0` | U9 | `FormulaArith/CarrySave.lean` | `fa` |
| 5 | `aa442e1db2a3b956f8de2b973fee174b432ceedd` | U10 | `FormulaArith/Compare.lean` | `fa` |
| 6 | `c8f2d23f759f5efeb984469939d819f08c1da44e` | U7 | `CircuitComplexity/NANDLayering.lean` | `layer`, plus the lead's edits (§4) |
| 7 | `bb7efa82af89141535e7a4adc49c6d97aef85de8` | U4 | `BranchingPrograms/BarringtonConverse.lean` (one helper sketch) | lead |

Each commit touches exactly one owned file. All are unsigned (`git -c commit.gpgsign=false`); `patches/COMMITS.tsv` has the signing column, all `none`. To land U4, take commits 3 and 7.

## 2. Preflight, cache, pool, who did what

- **Preflight** (`evidence/logs/preflight.log`):
  - `nproc` 4.
  - No cgroup memory limit (v1 limit 9223372036854771712; no v2 files), so the headroom is `MemAvailable` = 15.14 GiB (floor 4): **pass**.
  - Disk: 14.56 GiB free on ext4 (floor 12): **pass**.
  - To reach the disk floor, I first deleted my own previous job's scratch clone (`gsw6a`, job `gsw-6a-statements`, delivered at `d7a9adb5`). Its two local branches are kept as refs. Nothing was copied, moved or deduplicated.
- **Cache.**
  - 65 Mathlib roots, from the addendum's command. The pack's `roots.txt` adds `Std.Sat.CNF`, a Lean core module (`roots-note.txt`).
  - The cache tool's archive store held 3,609 archives (183,702,538 B) from my earlier job in this session on this host.
  - The narrowed `lake exe cache get` exited 0 with "No files to download; Decompressing 2487 file(s)". A first attempt died at once with `lake` not on the background shell's `PATH` (rc 127, `cache-get-attempt0-nopath.log`).
  - 0 empty oleans. Every present package matches the manifest. `doc-gen4`, `UnicodeBasic`, `BibtexQuery` and `MD4Lean` are ABSENT, and nothing in the order imports them (`RESULT present_mismatches=0`).
  - The cache probe compiles (rc 0).
  - For the one added Mathlib import, `Mathlib.Data.List.MinMax` (§4, U7), its root was fetched the same way, alone, with no Lean process running: rc 0 (`cache-get-added.log`, `mathlib-roots-added.txt`). The package check after it is again 0 mismatches.
- **Pool** (`evidence/logs/pool.log`):
  - A counting semaphore of `flock` slot files shared by all agents (`tools/lead/poollib.py`, `pool_run.py`).
  - Its size is `min(nproc 4, MemAvailable/4 GB = 4) = 4`, run at **3**. A slot starts only while `MemAvailable ≥ 2.5 GB`.
  - It was never resized. The `SIZE 0` line marks the interval in which the cache tool ran alone: no Lean process ran, and the size file stayed 3.
  - No shortage.
  - **Peak memory:** 4,019,396 KiB (`Parity`, bootstrap). Sub-agents peaked at 1,860,404 KiB (`bp`), 1,906,512 KiB (`fa`) and 1,984,944 KiB (`layer`). 442 pool runs in all.
- **Who did what:**
  - **Lead (main session):** setup, bootstrap, U5 and U11, integration and review of U4, U7, U9 and U10, the U7 import and helper body, two sketches, every check and both deliveries.
  - **Sub-agent `bp`:** U4. **Sub-agent `fa`:** U9 and U10. **Sub-agent `layer`:** U7.
  - Each sub-agent had its own worktree and olean tree, with `.lake/packages` linked to the lead's. The tree seeding is in `evidence/build/seed-check.txt`.
  - Their logs, searches, snapshots and reports are in `evidence/subagents/<name>/` (`REPORT-bp.md`, `REPORT-fa.md`, `REPORT-layer.md`). The shared rules are in `evidence/subagents/SUBAGENT-COMMON.md`.
  - Only the lead ran `lake`, committed and pushed.

## 3. The six files

| Unit | File | Base | Head | Fill | r3 §H7 | Max width |
|---|---|---|---|---|---|---|
| U4 | `BranchingPrograms/BarringtonConverse.lean` | 304 | 553 | +249 | 250–400 | 100 |
| U5 | `BranchingPrograms/NC1.lean` | 135 | 266 | +131 | 180–320 | 100 |
| U7 | `CircuitComplexity/NANDLayering.lean` | 388 | 947 | +559 | 150–250 (to ~300) | 100 |
| U9 | `FormulaArith/CarrySave.lean` | 297 | 665 | +368 | 250–400 | 99 |
| U10 | `FormulaArith/Compare.lean` | 238 | 556 | +318 | 150–250 | 100 |
| U11 | `FormulaArith/ModSum.lean` | 196 | 444 | +248 | 150–250 | 100 |

The total fill is +1,873 lines, against r3's 1,130–1,870 (`evidence/sizes/sizes-final.txt`). U7 and U10 are over their estimates: see GF-W3, and for U10, §7 (about 51 of its lines are helpers that privacy forced it to duplicate). Every file is under 1,000 lines. `NANDLayering` (947) is over policy's 600 target.

## 4. Per unit

Each unit's full detail is in the corresponding sub-agent report: every helper's docstring formula, the readers per target, and every refreshed sketch with its old and new text. Summaries follow.

### U4 `BarringtonConverse` (`bp`; `evidence/subagents/bp/REPORT-bp.md`)

**Proved:** C17 `Instr.wire_eval`, `Instr.depth_wire_le`, `Instr.maxFanin_wire_le`; C18 `wireComp_eval`, `depth_wireComp_le`; C19 `compTree_eval`, `depth_compTree_le`, `maxFanin_compTree_le`; C20 `toFormula_eval`; C21 `depth_toFormula_le`, `maxFanin_toFormula_le`.

**Private helpers (6):**
- `maxDepth_le_of_forall`: `(∀ c ∈ cs, c.depth ≤ d) → TreeCircuit.maxDepth cs ≤ d`.
- `maxFaninL_le_of_forall`: the same for `maxFaninL`.
- `maxFanin_wireComp_le`: fan-in-2 wires give `(wireComp F G i k).maxFanin ≤ 2`.
- `compTree_eval_list`: `(compTree l i j).eval x = decide ((⟨l⟩ : BranchingProgram w n).yield x i = j)`.
- `depth_compTree_list_le`: `(compTree l i j).depth ≤ (Nat.clog 2 w + 2) * Nat.clog 2 l.length + 1`.
- `maxFanin_compTree_list_le`: `(compTree l i j).maxFanin ≤ 2`.

The last three are well-founded on `l.length`.

**Readers used:**
- Defs: `Instr.eval_eq`, `yield_eq`, `append_instrs`, `length_eq`, and C1 `yield_nil`/`yield_append` (frozen).
- Basic: `eval_lit`, `Lit.eval_eq`, `depth_lit`, `maxFanin_lit`, `eval_node_true_iff`/`_false_iff`, `maxDepth_*`, `maxFaninL_*`.
- O1: `balanced_eval`, `depth_balanced_le`, `maxFanin_balanced_le`.
- U8's F3, frozen, beyond the brief's expectation: `const_eq`, `const_eval`, `depth_const`, `maxFanin_const`, `and2_eq`, `and2_eval`, `depth_and2_le`, `maxFanin_and2_le`. Used so as not to re-derive published facts about empty and binary gates. The axiom trace therefore names F3 for U4 as well as C1.
- The file's own readers.

**Import:** `Mathlib.Data.Fintype.BigOperators`, approved by the lead (`evidence/lead/decisions.md`, `evidence/subagents/bp/scope-request/`). It reuses `Fintype.card_fun` and `Finset.card_le_univ` and supplies the Pi `Fintype` instance for `|F| ≤ w^w`. It is already a cache root (l.21).

**Sketches:** all 11 refreshed (`bp/sketch-refresh.json`). Module sentence: "(targets admitted with `sorry`)" became "(targets proved here)". The lead added a sketch to `maxFanin_compTree_list_le` (commit 7).

### U5 `NC1` (lead)

**Proved:** C22 `exists_fiveCycleRecognizes_of_dagCircuit`; C23 `Language.InNC.inPBP_five`; C24 `Language.InBWBP.inNC_one`; C25 `Language.inNC_one_iff_inBWBP`, `Language.inNC_one_iff_inPBP_five`.

**No helper.** The `n = 0` case goes through the accepting set (`{id}` or `∅`, r3 §H8 item 7).

**Readers used:**
- `DAGCircuit.isFaninTwo_iff`, `isWellFormed_iff`, `toTree_eval`, `toTree_depth_le`, `toTree_maxFanin_le`.
- `Language.inTreeNC_iff`, `TreeCircuitFamily.hasFaninTwo_iff`/`isPolySize_iff`/`hasPolylogDepth_iff`/`mem_language_iff`.
- `Language.InNC.inTreeNC_one`, `Language.InTreeNC.inNC`, `BoolCircuit.clog_poly_le`, `TreeCircuit.size_succ_le_two_pow`.
- `BranchingProgramFamily.isPermutation_iff`/`isPolyLength_iff`/`mem_language_iff`, `Language.inPBP_iff`/`inBWBP_iff`.
- `fiveCycleRecognizes_iff`, `isFiveCycle_iff`.
- C1 `yield_nil`; C9 `isFiveCycle_sigma1`; C13 `barrington_recognizes`; C14 `barrington_length_le`; C15 `isPermutation_barrington`; U4's C20–C21.
- Mathlib `Equiv.Perm.cycleType_one`, `Nat.pow_log_le_self`.

**Sketches:**
- C22: "missing at the base and proposed" was removed after `isWellFormed_iff`.
- C23: "(read through readers of `Language.InTreeNC`, …, missing at the base and proposed)" became "(read through the readers `Language.inTreeNC_iff`, `TreeCircuitFamily.hasFaninTwo_iff` and `hasPolylogDepth_iff`)". Also added: "and `⇑sigma1 ≠ id` (a five-cycle has `cycleType {5}`: …)".
- C24: the constant `b = (⌈log₂ w⌉ + 2)(a + k) + topDepth w` is now named, and the proposed readers are now the four named readers.
- Module sentence: ", proved in the fill phase (gsw-6a-fills)".

### U7 `NANDLayering` (`layer`; `evidence/subagents/layer/REPORT-layer.md`)

**Proved:** N12 `layerGates_acyclic` (in the `args_lt` field form, 6a Q4 A), N13 `layerOutput_lt`, N7 `layerNAND_eval`, N8 `layerNAND_isLayered`, N9 `layerNAND_isNANDForm`, N10 `layerNAND_depth`, N11 `layerNAND_size_le`.

**The column invariant** is stated through private lemmas only; there is no private `def`.
- *Structural, before N12 (no `layerNAND`):* `layerChain_isPrefix`, `length_layerChain_fst`, `mem_layerChain_fst`, `layerChain_acyclic`, `layerAt_lt`, `layerColumn_struct`, `layerFold_struct`.
- *Semantic, over `layerNAND`:* `layerGates_isNAND`, `foldr_max_eq_of_forall`, `layerNAND_depthAt_snoc`, `layerNAND_values_snoc`, `layerNAND_single`, `layerNAND_values_lit`, `layerChain_col`, `layerNAND_link`, `layerColumn_sem`, `layerFold_sem`.
- The formulas are in `REPORT-layer.md` §3.

**Readers used:**
- `GatesAcyclic.nil/.snoc`, `gatesAcyclic_iff` (#360), `DAGCircuit.depthAt_gate`, `depthAt_eq`, `depthAt_input`, `DAGGate.depth_eq`, `DAGGate.getD_lt_depth`.
- `values_getD_gate`, `values_getD_input`, `all_congr_mem`, `depth_eq`, `eval_eq`, `size_eq`, `isNANDForm_iff`, `DAGGate.isNAND_iff`.
- U6's N1 `DAGGate.eval_of_isNAND` (frozen); the fields `C.args_lt`, `C.output_lt`; the file's own readers and `layerNAND_gates`/`_output`.

**The lead's edits before committing:**
- `layer`'s `foldr_max_eq_of_forall` (`(∀ y ∈ l, y = k) → y₀ ∈ l → l.foldr max 0 = k` on `ℕ`) re-proved by induction the `≤` direction that Mathlib publishes as `List.max_le_of_forall_le`. That would be a re-derivation (G48-01).
  - I added `import Mathlib.Data.List.MinMax`, after fetching its root as the addendum requires (§2).
  - The helper's body is now `le_antisymm (List.max_le_of_forall_le …) (List.le_max_of_le …)` after `Nat.bot_eq_zero`, and its docstring names them.
  - The helper itself stays, private, as glue for the `foldr max 0` shape of the `depthAt_gate` reader.
- Two sketches were added: `layerFold_sem` (`style_lint` flagged a 24-line proof) and `layerFold_struct` (20 lines).

**Sketches:** N12, N13 and N7's last sentence were refreshed; N8–N11 already described the proofs (old and new texts in `REPORT-layer.md` §6).

**Module docstring:**
- The admission sentence "…, so while they are admitted `sorryAx` reaches `layerNAND` through them only." became "…; they are proved here, structurally (no NAND-form hypothesis, no admitted lemma), so no admission reaches `layerNAND` through them."
- **G6A-F07 done:** the [Bar89] line now reads "D. A. Mix Barrington, … J. Comput. System Sci. 38(1):150–164, 1989." (the wording of `Barrington.lean:61–62`, kept on 2 lines).
- The frozen `layerNAND` docstring is now stale (GF-W2).

**Axioms:** N8 and N10 reach N1 only because the depth and value parts of the invariant are proved together in `layerColumn_sem`. Splitting them would cost about 40 lines. This is allowed: N1 is an in-house frozen target.

### U9 `CarrySave` and U10 `Compare` (`fa`; `evidence/subagents/fa/REPORT-fa.md`)

**Proved:**
- U9: F5 `csaStep_val`, `depth_csaStep_le`, `maxFaninL_csaStep_le`; F6 `csaReduce_val`, `depth_csaReduce_le`, `maxFaninL_csaReduce_le`, `csaLevels_le` (the settled `2⌈log₂ k⌉`, by strong induction; one `omega` covers the step `k₂ ≤ ⌈k/2⌉` for every `k`).
- U10: F7 `carryOut_eval`, `carryOut_eval_le`, `depth_carryOut_le`, `maxFanin_carryOut_le`; F8 `geConst_eval`, `depth_geConst_le`, `maxFanin_geConst_le`.

**U9 private helpers:**
- `maxDepth_le_of_forall`, `maxFaninL_le_of_forall`, `prefixVal_eq_of_false`, `val_eq_prefixVal_getD`, `prefixVal_fullAdder` (the full-adder identity, summed), `depth_getD_le`, `maxFanin_getD_le`.
- The own-definition layer lemmas `sum_csaLayer`, `length_csaLayer`, `length_repeat_csaLayer`, `iterate_csaLevels_le_two`, `mem_flatten_of_mem_getD`, `depth_csaLayer_le`, `maxFanin_csaLayer_le`.

**U10 private helpers:** `maxDepth_le_of_forall`, `maxFaninL_le_of_forall`, `prefixVal_eq_of_false`, `eval_getD_const`, `val_eq_prefixVal_bitAt`, `depth_getD_le`, `maxFanin_getD_le`, `carryBit_eq_true_iff` (the generate/propagate form), and `prefixVal_testBit`.

**Readers used:**
- Adder: `bitsVal_eq_prefixVal`, `prefixVal_zero/_succ/_congr/_lt`, `prefixVal_add`, `carryBit_zero/_succ` (#360); `sumBit` only inside `prefixVal_lt`.
- Basic's list readers; U8's F3 (frozen); O1's `balanced` lemmas.
- U10 reads `val`/`csaStep` only through `val_eq`, `csaStep_eq` and U9's targets.

**Imports:** none. **Sketches:** all 14 refreshed (`fa/sketches-*.json`). The module docstrings are unchanged.

### U11 `ModSum` (lead)

**Proved:** F9 `modSumInterval_eval`; F10 `depth_modSumInterval_le`, `modSumDepth_le`, `maxFanin_modSumInterval_le`.

**Private helpers:**
- `maxDepth_le_of_forall`, `maxFaninL_le_of_forall`.
- `prefixVal_testBit`: `prefixVal c.testBit p = c % 2 ^ p`.
- `val_maskedConst`: `a < 2 ^ p → val x (maskedConst i a p) = (x i).toNat * a`.
- `prefixVal_eq_of_lt_two_pow`: `w ≤ m → prefixVal f m < 2 ^ w → prefixVal f m = prefixVal f w`.
- `val_take_of_lt`: `val x U < 2 ^ w → val x (U.take w) = val x U`.

**Readers used:**
- U9 and U10's targets and readers (`val_eq`, `csaReduce_val`, `depth_csaReduce_le`, `maxFaninL_csaReduce_le`, `csaLevels_le`, `geConst_eval`, `depth_geConst_le`, `maxFanin_geConst_le`); its own `maskedConst_eq`, `modSumInterval_eq`, `modSumDepth_eq`.
- U8's F1–F3 (frozen); O1; Basic; Adder.
- Core `Nat.mod_pow_succ`, `Nat.toNat_testBit`; Mathlib `List.sum_ofFn`, `Finset.sum_le_sum`, `Nat.div_eq_of_lt_le`.

**Imports:** `Mathlib.Algebra.BigOperators.Fin` and `Mathlib.Algebra.Order.BigOperators.Group.Finset` (cache roots l.1, l.4), for `List.sum_ofFn` and `Finset.sum_le_sum`.

**Sketches:**
- F9 (1) and (3) now name `val_maskedConst`, `Lit.eval_eq`, `prefixVal_testBit` and `val_take_of_lt`, and the bound `S ≤ M (q - 1) < 2 ^ w`.
- F10 names `depth_lit`, `maxFanin_lit`, `List.mem_of_mem_take` and `maxDepth_le_of_forall` instead of "reader missing".
- `val_maskedConst` has its own sketch.
- F9's `lo ≤ hi` stays and is unused (G6A-F09).

## 5. Statement changes

None. decls2 reports 0/0/0, the StmtDump is identical, and the frozen check passes.

## 6. Checks

1. **Bootstrap and sweep.**
   - The bootstrap of `order.txt` at the base: 218/218 rc 0, 0 errors in both forms. Exactly the 115 `sorry` declarations in 18 modules of `base-sorries.txt`, name by name.
   - Every source equals `SOURCE-SHA256SUMS` (`evidence/build/bootstrap/`, `source-binding.txt`).
   - **Sweep at the head**: each changed module and its downstream were rebuilt in order at every integration (`evidence/lead/*-integration/`). The final sweep over the 9 DOWN modules gave 9/9 rc 0, 0 errors in both forms, 0 `sorry`, each source bound to `git show HEAD` (`evidence/build/sweep-final/summary.txt`, `RESULT modules=9 bad=0`).
   - The root `TCSlib` is not built.
2. **Admissions:** **74 declarations in 12 modules** = `base-sorries.txt` minus the 41 targets, 0 mismatches (`evidence/admissions/admissions-final.txt`). No `sorry` token in any owned file (`sorry-tokens-final.txt`: all 0).
3. **Statements:**
   - `decls2.py . 05999162 <six files>`: **0 ADDED, 0 CHANGED, 0 REMOVED** (`evidence/stmt/decls2-final.txt`).
   - `StmtDump` of the 41 targets (full names, `pp.fullNames`) is identical at base and head (`StmtDump-base.log`, `StmtDump-head-final.log`).
   - **Frozen check** (`evidence/headers/frozen_owned.py`, its header gives the method): 6/6 files PASS with 0 differences (`frozen-final.txt`), against `allow.tsv`, which licenses:
     - the three admission sentences (U4, U5, U7);
     - the G6A-F07 line (U7);
     - the four Mathlib imports (U4, U7, U11 ×2).
   - Controls, per file:
     - a one-character header change, a sketch edit spilling into the statement prose, a definition-body edit, a reader edit and an unpermitted import each FAIL with exactly 1 difference;
     - a deleted target FAILs with 2 (the missing target and its hunk);
     - `NC1` has no definition or reader, so those two controls are N/A there.
   - The unchanged files PASS (`frozen-base-vs-base.txt`).
4. **Axioms** (`evidence/axioms/AxiomProbe-final.log`, `trace-check-final.txt`):
   - The census covers 386 stored constants of the six modules, auxiliaries included. Their axioms are `propext`, `Classical.choice`, `Quot.sound` and `sorryAx`.
   - The dependency trace walks every TCSlib constant. Every one of the 57 constants reaching `sorryAx` reaches it only through admitted declarations of the in-house modules (`bad=0`):
     - **U4:** C1 `yield_append`, `yield_nil`; F3 (`const_eval`, `depth_const`, `maxFanin_const`, `and2_eval`, `depth_and2_le`, `maxFanin_and2_le`).
     - **U5:** C1; C9 `isFiveCycle_sigma1`; C13 `barrington_recognizes`; C14 `barrington_length_le`; C15 `isPermutation_barrington`; F3 through U4.
     - **U7:** N1 `DAGGate.eval_of_isNAND` only.
     - **U9–U11:** U8's F1–F3 only (`const_*`, `and2_*`, `or2_*`, `xor3_*`, `maj3_*`, `neg_*`).
   - No declaration of an owned file is admitted.
   - **G6A-F14:** `layerNAND`, `layerNAND_gates` and `layerNAND_output` have **empty traces**.
5. **Rule 10.**
   - **Seals** A, B, coe-A and coe-B, with `-DmaxErrors=0`, over the full TCSlib import closure. Every probe has rc 0, 0 errors, and its install and EOF records.
     - Head (`evidence/rule10/final-head/seal-*.tsv`): BarringtonConverse 243, NC1 336, NANDLayering 187, CarrySave 253, Compare 275, ModSum 280 requests.
     - Base (`cp1-base` for U4, U5, U11; `base-rest` for U7, U9, U10): 243, 333, 187, 253, 269, 273, equal to the maintainer's #359 reference.
     - The head's extra requests (NC1 +3, Compare +6, ModSum +7) are exactly the `match_1_1` auxiliaries of the new private helpers of the files they import (listed in the analysis log).
   - **No failing declaration.** No strict-only failure; the notation exclusions were not needed.
   - **Liveness pairs** (`evidence/rule10/live-final/summary.txt`; sources in `probe-sources/live`). Each is appended to the owner's own full seal probe, so it runs in a consumer's context:

     | Owner | Foreign definition | Negative | Reader |
     |---|---|---|---|
     | U4 | `BranchingProgram.yield` | `rfl` | `yield_eq` |
     | U5 | `DAGCircuit.IsWellFormed` | `Iff.rfl` | `isWellFormed_iff` |
     | U7 | `DAGCircuit.IsNANDForm` | `Iff.rfl` | `isNANDForm_iff` |
     | U9 | `prefixVal` | `rfl` | `prefixVal_succ` |
     | U10 | `carryBit` | `rfl` | `carryBit_succ` |
     | U11 | `FormulaArith.val` | `rfl` | `val_eq` |

     The unsealed negatives were pretested first: 0 errors. Sealed, every negative has exactly 1 error and every positive 0. **A `ALL_OK True`, coe-A `ALL_OK True`.**
   - **Explicit-unfold scan** over the six files: **0 foreign** (`final-head/explicit-unfold-scan.txt`).
6. **Frozen files:** `git diff --stat 05999162 HEAD` lists only the six owned files (`evidence/git-diff-stat-final.txt`).
7. **Lint:**
   - `style_lint` on the six files: 0 findings (`evidence/lint/style-head-final.txt`).
   - `campaign_style_lint TCSlib/Complexity --check8b`: **25 FAIL / 390 WARN over 513 files** at base and head, with identical FAIL/WARN line sets (`campaign-diff-final.txt` is empty).
8. **Sizes:** §3 (`sizes_fill.py`). No line over 100, no file over 1,000.
9. **Docstrings** (`evidence/docs/hygiene-final.txt`):
   - 52 new private helpers, 0 without a formula or "Glue.". CarrySave's two base-private declarations (`csaLevelsAux`, `csaLevelsAux_fuel`) are frozen and listed separately.
   - 32 declarations of 20 or more lines (statement through proof), 0 without `**Proof sketch.**`. Long proofs have `-- Step` comments.
10. **Clash and shadow** (`evidence/clash/clash-final.txt`):
    - 52 new names, all private, none existing in `TCSlib/` or `audits/` at the base, none containing `NAnd` or `toLayered`.
    - No new short name exists elsewhere at the base, so no unqualified use in a DOWN module can change resolution.
    - The same private names in several of the six files (§7) are distinct constants (`_private.<module>.0.…`) and are not visible across modules; the head builds.
11. **Reuse and overlap:** §7.
12. **Reproduction:**
    - `git am` of `patches/` at the base, in a scratch clone with each commit's committer identity and date from `COMMITS.tsv`, reproduces all 7 hashes (`evidence/reproduce-final.log`).
    - The scratch clone is a shared partial clone of the same remote, sparse like the work clone, because the blobless work clone does not hold `briefs/` blobs.
    - `src/` equals the head's six files byte for byte (made by `git show HEAD:<path>`).

## 7. Overlap and reuse

**Searches.**
- Lead: `evidence/lead/searches.md`.
- Sub-agents: `evidence/subagents/{bp,fa,layer}/searches.md`, with grep over TCSlib, Mathlib, Batteries and core, and `exact?` probes (`layer` `DupNL-001`).

**Reuse in place of re-derivation:**
- the readers of #360 throughout;
- U8's F1–F3 in U4 and U9–U11;
- Mathlib `Fintype.card_fun` (U4 import), `List.sum_ofFn` and `Finset.sum_le_sum` (U11 imports), `List.max_le_of_forall_le` and `List.le_max_of_le` (U7 import);
- core `Nat.mod_pow_succ` and `Nat.toNat_testBit`;
- TCSlib `clog_poly_le` and `size_succ_le_two_pow`.

**Private helpers proved in more than one owned file** (`evidence/overlap/dup-inventory.txt`). These are forced: each file is foreign to the others and helpers must be private.

| Helper | Files | Lines each |
|---|---|---|
| `maxDepth_le_of_forall` | U4, U9, U10, U11 | 9 |
| `maxFaninL_le_of_forall` | U4, U9, U10, U11 | 9 |
| `prefixVal_eq_of_false` | U9, U10 | 8 |
| `depth_getD_le` | U9, U10 | 9 |
| `maxFanin_getD_le` | U9, U10 | 10 |
| `prefixVal_testBit` | U10, U11 | 6–7 |

- U9's `val_eq_prefixVal_getD` and U10's `val_eq_prefixVal_bitAt` state one fact in two shapes.
- Copied lines per file, against its fill: U4 18 (7.2%), U9 45 (12.2%), U10 51 (16.0%), U11 25 (10.1%), U5 and U7 0. No file reaches one fifth.
- Disclosure is not acceptance (G44-01): see GF-W1.

**Nearest TCSlib relatives, not copied:**
- `Basic.lean:265` `depth_le_maxDepth` and `:273` `maxFanin_le_maxFaninL` are the converse direction.
- Private `TreeNCAC.lean:215,226` (`maxDepth_map_le`, `maxFaninL_map_le`) and `TreeDAG.lean:407,420` (`maxDepth_map`, `maxFaninL_map`) have other forms.
- `LupanovGates.lean:123` `testBit_ofBits` has no bridge to `Adder.bitsVal`.
- `AdderLanguage.lean:72` `bitsVal_natToBits` needs a reader of `natToBits`'s entries.
- Core's `Nat.mod_two_pow_succ` (`Init/Data/BitVec/Bitblast.lean:163`) is private.
- For `foldr_max_eq_of_forall`, there are private TCSlib inequality variants (`TQBFHardTseitin.lean:99`, `LogspaceUniformCanon.lean:51`). The helper is now built from Mathlib's pair.

**Inline facts:**
- U5 states `⇑sigma1 ≠ id` from `isFiveCycle_iff` and `cycleType_one`; no `IsFiveCycle.ne_one` exists.
- U5 has a calc bound `4^(b(log n+1)) ≤ 4^b (n+1)^(2b)`, as NCAC's `inTreeNC_one` does inline.
- U7's `foldr_max_eq_of_forall` cites Mathlib after the lead's edit (§4).

## 8. Promotion and scope requests

**Promotion requests** (the helpers live `private` until then):
- **P1:** `TreeCircuit.maxDepth_le_of_forall` and `maxFaninL_le_of_forall` to `Basic.lean`. This removes the 4×2 copies.
- **P2:** `prefixVal_testBit`, `prefixVal_eq_of_false`, `prefixVal_eq_of_lt_two_pow`, `prefixVal_fullAdder` and `carryBit_eq_true_iff` to `Adder.lean`.
- **P3:** `depth_getD_le` and `maxFanin_getD_le` (padded list reads) to `Combinators.lean` or `Basic.lean`.
- **P4:** a public padded-value reader for `FormulaArith.val` in `CarrySave.lean`, which would remove the `val_eq_prefixVal_*` overlap.
- **P5:** `foldr_max_eq_of_forall` to a shared list file, or a `depthAt_gate` reader in `List.foldr max ⊥` form.

**Scope requests:** none. The only import request, `bp`'s, is within the brief's *Imports* rule and was decided by the lead. The lead's own imports are disclosed in §4.

## 9. Questions for Seyoon

- **GF-W1 (duplicated private helpers across the six files, §7).**
  - (A, recommended) Accept them as recorded duplication debt, and land promotions P1–P4 as one owner-side PR after the units land. That PR deletes the private copies, so a later landing edit removes them.
  - (B) Approve a scope request now: add P1 and P2 to `Basic.lean`/`Adder.lean` before landing, and re-issue the files with the copies removed.
- **GF-W2 (stale frozen docstring).** The frozen `layerNAND` docstring (`NANDLayering.lean`, "While N12 and N13 are admitted, `sorryAx` reaches it through them only") is now false: N12 and N13 are proved, and the trace is empty.
  - (A, recommended) A one-line landing edit by the maintainer.
  - (B) Leave it until the next docstring sweep.
- **GF-W3 (size of `NANDLayering.lean`).** 947 lines: under 1,000 but over policy's 600 target and r3's 150–300 fill. The fold-step case split is proved twice, structurally for N12 (which cannot use `layerNAND`) and semantically for N7, N8 and N10. `layer` estimates that one merged invariant over `runWith` would save about 100–150 lines.
  - (A, recommended) Accept as is.
  - (B) A compaction re-issue.
  - (C) Split the file in a later owner-side PR.

## 10. Evidence

`evidence/` with its manifest `evidence/SHA256SUMS`, and the top-level `SHA256SUMS` (paths equal to the delivered files):
- `logs/`: preflight, cache, packages, roots, `pool.log`, mkbase and the merge recipe.
- `build/`: the bootstrap with its source binding, the seeds, the base DOWN rebuild, and the checkpoint and final sweeps.
- `admissions/`; `stmt/`: decls2, StmtDump; `headers/`: the frozen check and its controls.
- `axioms/`: probe, census, trace.
- `rule10/`: seals at head and base, probe sources, liveness pairs, unfold scans.
- `lint/`, `sizes/`, `docs/`, `clash/`, `overlap/`, `outlines/` (checkpoint 1).
- `lead/`: logs, searches, decisions, integration builds. `subagents/`: the three sub-agents' logs, probes, snapshots, searches and reports, and the shared rules.
- `tools/`:
  - `lead/`: this job's tools, each with its header.
  - `stmt/`: the statement job's tools, adapted to the pool, each change noted in its header.
  - `records/`: `decls2.py` and the records inputs.
- `git-merge-tree-{cp1,final}.txt`, `git-diff-stat-{cp1,final}.txt`, `reproduce-{cp1,final}.log`, `final-checks.log`.
