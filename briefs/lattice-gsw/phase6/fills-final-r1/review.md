# gsw-6a-fills · final r1 · phase-1 (static) maintainer review

**Interim verdict: ACCEPT WITH LANDING EDITS, pending phase 2 and three rulings (GF-W1–W3).** There is no
blocker. There are two majors:
- **GF-F01**, undisclosed: an inline re-derivation of Mathlib's `Nat.pow_log_le_add_one` in C24, with a sibling in
  C23. This is the G48-01 pattern. It is closed by the landing edit LE-gf1 (a 2-line reuse).
- **GF-F02**, disclosed: 16 private declarations in 6 helper families across four files. That is 10 redundant
  copies, and 12 of the 16 are byte-identical within their family. This is the worker's GF-W1.
  Under policy §1 and G44-01 it needs Seyoon's acceptance or repayment.
  - Recommended: repay at landing with LE-gf3. Two helpers are promoted to `Basic.lean` and two to `Adder.lean`
    (a #360 addendum, like `cc05f76c`), and two `CarrySave` helpers are made public.
  - The alternative is a ledger row, DL-61.

There are two minors (GF-F03, GF-F04) and five infos.

The delivery proves all 41 targets in the six owned files.
- **Reproduction and integrity:** both manifests pass with exact path sets. `mkbase.sh` gives `05999162…`. The 7
  patches reproduce `bb7efa82af89141535e7a4adc49c6d97aef85de8` hash for hash, and `src/` is byte-identical.
- **Scope:** only the six files change. Outside proof bodies, sketches and private helpers, the only changes are the
  permitted sentences, the G6A-F07 line and four Mathlib imports. decls2 gives 0/0/0.
- **Admissions:** 74 in 12 modules, none in the owned files.
- **Recounted from the raw logs:** seals, liveness controls, the axiom trace and the sweep. With G6A-F14 met, no
  admission reaches `layerNAND`.

I ran no Lean. Phase 2 replays the head and the landing edits on olean snapshot #6.

## What was reviewed

- **Delivery.** `inbox/fills/gsw-6a-fills/` on `exchange/pass-shelat-ch5-8`.
  - Final: `607034428468ffd88adec313eb293e3e60520f59` ("fill gsw-6a-fills: final").
  - Its parent is checkpoint 1, `ae6302979f31aad2ee73f49b2ec7bcf730dbb253`.
  - Both commits are unsigned (`gpgsig` 0) and touch only that path. No later exchange commit touches it (tip at
    review: `eae18c1b`).
  - I extracted the folder with `git archive` into an empty scratch directory: 956 files, namely `REPORT.md`
    (470 lines), 7 patches with `COMMITS.tsv`, `src/` (6 files), and `evidence/` (939 files plus its manifest).
- **Contract.** `issued-fills-r1/` (`brief.md`, the addendum, `targets.txt` with 41 targets, `base-sorries.txt`,
  `closures.txt`, `order.txt`, `roots.txt`, `tools/`), plan r3, `rulings.md`, `final-6a-r1/review.md`, the statement
  checkpoint review, and Gate 45 `findings-r1.md`.
- **Moved since dispatch.**
  - #359 is now `d154c8830fc8ffc52671b41992e7dbef61e30959` (LE-g45, LE-g45b): `eval_node_nil` moved into
    `Combinators`, and `const_eval` is proved.
  - #360 is now `cc05f76c43cd2d2f565ff0dfaec1c85b47e06d25`, adding `vertexValue_eq` and `vertexDepth_eq`.
  - The in-house branches are `fill/gsw-6a-u1-u2` `f31382a5…` and `fill/gsw-6a-u8-u6` `b65668a9…`.
  - The records tip is `2f83708f8dbf9e4e0715b9cb5d3a79f5ac3be6f7`. The worker's base predates all of these.

## Checks

| Check | Result |
|---|---|
| **Integrity** | Top `SHA256SUMS` (`792ab057…`): 955/955 OK. `evidence/SHA256SUMS` (`27364c36…`): 939/939 OK. Path sets are equal: the top manifest is the 954 other files plus `evidence/SHA256SUMS`, and the evidence manifest equals the 939 evidence files. No `./` and no symlinks. |
| **Base** | `issued-fills-r1/tools/mkbase.sh` prints `BASE 05999162b77c1f0fef64b07427e1a041a31b43d2 tree 7d551d6f5278fb79febe1b4eeffb4ca4329dc1d3`. |
| **Patches** | Worktree: sparse and detached at the base. Command: `git am` per patch, with that row's committer name, email and date from `COMMITS.tsv`, and `commit.gpgsign=false`. It reproduces all 7 hashes in order:<br>`59599399` U5, `9603797e` U11, `f437e0d0` U4, `9edc2be0` U9, `aa442e1d` U10, `c8f2d23f` U7, and `bb7efa82af89141535e7a4adc49c6d97aef85de8` U4 (a helper sketch).<br>Each commit touches exactly one owned file, and none has a `gpgsig`. `src/` is byte-identical to the head, 6/6. Head tree: `0e229d5f…`.<br>Checkpoint 1's `src/` (6 files) is byte-identical to `f437e0d0`. |
| **Scope** | `git diff --stat 05999162 bb7efa82`: exactly the six owned files, +2043/−170. |
| **decls2** (pinned `fa81981a…`, records copy) | **0 ADDED, 0 CHANGED, 0 REMOVED.** This equals the delivered `decls2-final.txt`. |
| **Frozen check** | **Worker's `frozen_owned.py`, re-run:** 6/6 PASS. All 34 applicable controls fail with the stated counts. The output is line-identical to `frozen-final.txt`.<br>**My independent `frozen2.py`** uses line-level difflib. Deleted base lines must lie in a target's sketch paragraph or proof body. Inserted head lines must lie in the same target's regions, in a new column-0 `private` block with its docstring, or in an `import Mathlib.` line.<br>Result: **12 residual lines, all permitted.**<br>• the admission sentence of U4 (`BarringtonConverse.lean:36`), U5 (`NC1.lean:28`) and U7 (`NANDLayering.lean:44–45`);<br>• the G6A-F07 [Bar89] line (`NANDLayering.lean:86–87`).<br>The header and prose controls fail in all 6 files. 52 new private helpers. |
| **Admissions** | My syntactic scan of the 218 modules of `order.txt`, with comments and strings stripped:<br>• base: 115 in 18, name-equal to `base-sorries.txt`;<br>• head: **74 in 12**, equal to base minus the six owned modules.<br>The owned files have 0 `sorry`, `admit`, `native_decide` or `axiom` tokens, no new `@[…]` attribute and no new `set_option`. The 3 `set_option`s per file are the policy header. |
| **Imports** | `Mathlib.Data.Fintype.BigOperators` (U4), `Mathlib.Algebra.BigOperators.Fin` and `…Order.BigOperators.Group.Finset` (U11), and `Mathlib.Data.List.MinMax` (U7). All four are in `roots.txt` (l.21, 1, 4, 37). REPORT's separate fetch of MinMax was therefore unnecessary but harmless. No TCSlib import was added. |
| **Rule 10, static** | Every name passed to `simp`/`rw`/`unfold`/`dsimp`/`simp_rw`/`erw`/`nth_rewrite` in the six files, 300 distinct, was classified (`rwnames.tsv`). They are theorems, hypotheses, or the file's own readers and definitions. **0 foreign definitions.** There is no `unfold` or `delta` anywhere in the added lines.<br>The `show`/`change` steps reduce only core `Nat.repeat` (CarrySave: `length_repeat_csaLayer`, `depth_csaReduce_le`, `maxFaninL_csaReduce_le`). The brief permits that for core definitions. Bare `dsimp only` occurs only for β/let reduction. |
| **Lint** | `style_lint` (base blob `87cb27d0`) on the six files: 0 findings. `campaign_style_lint TCSlib/Complexity --check8b` (blob `88a2256b`), run on my sparse base and head checkouts: **25 FAIL / 390 WARN over 513 files** at both, with identical FAIL/WARN line sets. |
| **Sizes, widths** | U4 304 → 553, U5 135 → 266, U7 388 → **947**, U9 297 → 665, U10 238 → 556, U11 196 → 444. Total fill +1,873 (r3: 1,130–1,870). The maximum width is 100. Over the 600 target: U7 and U9 (INFO in the lint). None is over 1,000. |
| **Docstrings, sketches** | My scan: all 52 helpers have a formula and "Glue.", and none carries a source tag. Every declaration block of 20 or more lines has a `**Proof sketch.**`. The only flags are frozen base declarations (CarrySave's private `csaLevelsAux`/`_fuel`; `decidableIsLayered`). I spot-read the U5, U9 and U11 sketches against their proofs: they describe the delivered proofs. |
| **Clash, shadow** | None of the 44 distinct helper short names is declared anywhere else in `TCSlib/` or `audits/` at the base. None is among the names added by `d154c883`, `cc05f76c`, `f31382a5`, `b65668a9` or the records tip. |

## Recount of the worker's evidence (raw logs, not REPORT)

- **Sweep** (`build/sweep-final`): 9/9 modules, rc 0, and 0 errors in both forms (`^\S+\.lean:\d+:\d+: error[:(]`
  and any `error`). 0 `sorry` warnings and 0 warnings in all. Each summary SHA-256 equals `git show bb7efa82:<file>`
  of my reproduced head, 9/9.
- **Bootstrap** (`build/bootstrap`): 218 logs, 0 errors, 115 `sorry` warnings in 18 modules.
- **Seals** (`sealcount.py`): 60 seal probes over 4 sites × 4 variants, all OK. The sites are final-head (6 owners),
  base-rest (U7, U9, U10), cp1-base (U4, U5, U11) and cp1-head. For each probe:
  - the probe hashes to `probe_sha256`;
  - each recorded insertion is hash-checked;
  - removing the insertions gives back `git show <rev>:<owner>` byte for byte (head `bb7efa82`, base `05999162`,
    cp1 `f437e0d0`);
  - the raw log hashes to `log_sha256`, with rc 0 and 0 errors in both forms;
  - `G06-SEAL`, both `G06-MASK` (install and EOF, verified = requested) and `G06-SEAL-END` are present.
- **Seal request counts** (all four variants equal):
  - head: U4 243, U5 336, U7 187, U9 253, U10 275, U11 280;
  - base: 243, 333, 187, 253, 269, 273, the maintainer's #359 reference;
  - the deltas (+3, +6, +7) are exactly the `match_1_1` auxiliaries of the imported owners' new private helpers
    (`request-delta-vs-base.txt`).
  - Cross-owner sealing is live. For example, ModSum's seal installs 22 `CarrySave` and 5 `Compare` names, and
    NC1's installs 11 `BarringtonConverse` names.
- **Liveness pairs** (`live-final`): 30 runs, each bound by source and log hash.
  - The 6 unsealed negatives: rc 0, 0 errors.
  - The 12 sealed negatives (A and coe-A): exactly 1 error each, at the appended `example` line.
  - The 12 positives: 0 errors.
  - The foreign definitions read: `yield`, `IsWellFormed`, `IsNANDForm`, `prefixVal`, `carryBit` and
    `FormulaArith.val`.
- **Axioms** (`AxiomProbe-final.log`):
  - 386 stored constants. Axioms are `propext` 321, `Quot.sound` 293, `Classical.choice` 190 and `sorryAx` 57.
  - All 57 `sorryAx` constants have a TRACE line, and every `via` name is an admitted declaration of an in-house
    module at the base:
    - Defs: `yield_append`, `yield_nil`;
    - Barrington: `isFiveCycle_sigma1`, `barrington_recognizes`, `barrington_length_le`,
      `isPermutation_barrington`;
    - NANDForm: `DAGGate.eval_of_isNAND`;
    - Combinators: F1/F3 `const_*`, `and2_*`, `or2_*`, `xor3_*`, `maj3_*`, `neg_*`.
  - **0 bad.** No owned declaration is admitted, and no definition reaches `sorryAx`.
  - `layerNAND`, `layerNAND_gates` and `layerNAND_output` have the standard axioms only and no trace (G6A-F14 met).
  - U4 also reaches F3 (disclosed: it reuses `const_eval`/`and2_*` instead of re-deriving them). U7's N7, N8 and
    N10 reach N1 (disclosed).
  - After LE-g45, `const_eval` is proved, so those traces shrink at landing.
- **Unfold scan:** the worker's `explicit-unfold-scan.txt` reports 0 foreign, consistent with my `rwnames.tsv`.

## Duplication review (checklist item 6)

I searched every helper by name and by statement shape. Sources: `TCSlib/` at the base, the records tip, #359
`d154c883`, #360 `cc05f76c`, `f31382a5` and `b65668a9`; Mathlib `029db123`, Batteries and core v4.25.0 by grep. I
also read every proof body for inline `have`s of general facts. The log is `dup-searches.txt` in the evidence.

| Helper (or inline fact) | file:line at head | Closest existing lemma | Verdict | Proposed landing edit |
|---|---|---|---|---|
| inline `h2 : 2 ^ Nat.log 2 n ≤ n + 1` (case split on `n`) in C24 | `NC1.lean:228–231` | Mathlib `Nat.pow_log_le_add_one` (`Data/Nat/Log.lean:176`; already used by TCSlib `Parity.lean:360`) | **exact duplicate (re-derivation), undisclosed → GF-F01** | LE-gf1: `Nat.pow_log_le_add_one 2 n` |
| inline `h2` in C23 (`(pow_log_le_self 2 h0).trans (le_succ n)`) | `NC1.lean:147–148` | same | instance (one-term composition) | LE-gf1, same line |
| `maxDepth_le_of_forall` ×4 | `BarringtonConverse:247`, `CarrySave:70`, `Compare:67`, `ModSum:115` | none public; near: private `TreeNCAC.maxDepth_map_le` (base `:215`, map form); converse `Basic:265` `depth_le_maxDepth` | forced cross-file copy (4 copies, 3 byte-identical) → GF-F02 | LE-gf3: promote to `Basic.lean` as `TreeCircuit.maxDepth_le_of_forall`; delete 4 copies |
| `maxFaninL_le_of_forall` ×4 | `:257`, `:80`, `:77`, `:125` | private `TreeNCAC.maxFaninL_map_le` (`:226`) | forced copy → GF-F02 | LE-gf3: promote (`Basic.lean`); delete 4 |
| `prefixVal_eq_of_false` ×2 | `CarrySave:90`, `Compare:87` | none; near `Adder` `prefixVal_congr` (indices `< i` only) | forced copy (byte-identical) → GF-F02 | LE-gf3: promote to `Adder.lean`; delete 2 |
| `prefixVal_testBit` ×2 | `Compare:364`, `ModSum:135` | near: Batteries `Nat.ofBits_testBit` (`ofBits` form, no `prefixVal` bridge); core `Nat.mod_pow_succ` used | forced copy → GF-F02 | LE-gf3: promote to `Adder.lean`; delete 2 |
| `depth_getD_le`, `maxFanin_getD_le` ×2 | `CarrySave:214/224`, `Compare:115/125` | none (core `getD_eq_getElem`/`getD_eq_default`, `getElem_mem` used) | forced copy (byte-identical) → GF-F02 | LE-gf3: make `CarrySave`'s public; delete `Compare`'s |
| `val_eq_prefixVal_getD` / `val_eq_prefixVal_bitAt` | `CarrySave:100` / `Compare:104` | each other (Compare's own `bitAt` shape) | near (one fact, two shapes) | none now; record under DL-61 (P4) |
| `prefixVal_fullAdder` | `CarrySave:149` | `Adder:405` `prefixVal_add` (two operands, carry chain; same per-bit full-adder step inside its proof) | near, not an instance | none |
| `carryBit_eq_true_iff` | `Compare:171` | none (`carryBit_zero/_succ` only) | none | none (P2 promotion candidate) |
| `prefixVal_eq_of_lt_two_pow`, `val_take_of_lt`, `val_maskedConst` | `ModSum:174/189/147` | none | none | none |
| `foldr_max_eq_of_forall` | `NANDLayering:534` | Mathlib `List.max_le_of_forall_le` + `List.le_max_of_le` (body uses them, after the lead's fix); private TCSlib variants (`TQBFHardTseitin:99`, `LogspaceUniformCanon:51`, `Formulas/CNF:146`) | glue over Mathlib, not a re-derivation | none |
| `mem_flatten_of_mem_getD` | `CarrySave:453` | core `List.mem_flatten_of_mem` + `getElem_mem` (used) | none | none |
| U7 `layerNAND_depthAt_snoc`, `_values_snoc`, `_single`, `_values_lit` | `NANDLayering:543–579` | instances of the public `depthAt_gate`/`values_getD_gate`/`values_getD_input` via `IsPrefix.getElem`; **no `vertexDepth`/`vertexValue` ↔ `runWith` bridge in U7** (item b); NANDForm's private `depth_runWith_eq` (`b65668a9`) is at the `runWith` layer, not the same fact | none | none |
| U7 structural/semantic invariant (`layerChain_*`, `layerAt_lt`, `layerColumn_*`, `layerFold_*`, `layerGates_isNAND`) | `NANDLayering:273–833` | own definitions | none | none (GF-W3: size) |
| U4 `maxFanin_wireComp_le`, `compTree_eval_list`, `depth_compTree_list_le`, `maxFanin_compTree_list_le` | `BarringtonConverse:291–433` | own definitions (the list-recursive forms behind C19) | none | none |
| U9 `sum_csaLayer`, `length_csaLayer`, `length_repeat_csaLayer`, `iterate_csaLevels_le_two`, `depth_csaLayer_le`, `maxFanin_csaLayer_le` | `CarrySave:406–499` | own definitions | none | none |
| `eval_getD_const` | `Compare:96` | own `bitAt` with core `List.getD_map` | none | none |
| `eval_node_nil` / `const_eval` (item c) | — | — | **not restated**: U4 uses `← const_eq, const_eval`. Nothing reads `Hierarchy` | none |
| inline `hSle` (`Finset.sum_le_sum` + `Finset.sum_const`) | `ModSum:231–237` | Mathlib `Finset.sum_le_card_nsmul` (`Order/BigOperators/Group/Finset.lean:192`, imported) | near (two-lemma composition, not a re-proof) → GF-F03 | LE-gf4 (optional) |
| inline `⇑sigma1 ≠ id` | `NC1:116–121` | composes Mathlib `cycleType_one`, `Multiset.zero_ne_singleton` | none | none |
| inline `hclog : clog 2 (max M 1) = clog 2 M` | `ModSum` (F10) | composes `clog_one_right`/`clog_zero_right` | none | none |

**GF-W1 against the in-house units.** No worker helper overlaps the in-house private helpers:
- `f31382a5`: Barrington's `IsFiveCycle.*`, `*_ofPerm`, `commutatorProgram_*`, … and Eval's `stepWith_single`;
- `b65668a9`: Combinators' `pairUp`/`combineFuel`/`negList`/`substList` lemmas and NANDForm's `depth_runWith_eq` and
  `gadgetSpec_*`.

The in-house `depth_subst_le`/`maxFanin_subst_le` (`b65668a9`, `Combinators.lean:441–491`) contain an inline list
induction of the same kind as `maxDepth_le_of_forall`, in a `+ D` shape. After LE-gf3 that induction and TreeNCAC's
private pair can reuse the promoted lemma. That goes on the dedup queue, not this landing.

## Findings

| ID | Severity | Location | Finding | Disposition |
|---|---|---|---|---|
| **GF-F01** | **major** | `NC1.lean:228–231` (C24), `:147–148` (C23) | C24 proves `2 ^ Nat.log 2 n ≤ n + 1` by a case split on `n`. That is exactly Mathlib's `Nat.pow_log_le_add_one 2 n`, which TCSlib already uses (`Parity.lean:360`). C23 builds the same bound from `pow_log_le_self` (`n ≠ 0`). The re-derivation is undisclosed. REPORT §7 discloses only the calc it sits in, and the lead's search was TCSlib-only (`lead/searches.md:31`). This is the G48-01 pattern (Codex graded major; Seyoon's revised ruling: fix at once by a landing edit). | **LE-gf1** (−8/+5, sketches synced). No ledger row needed. |
| **GF-F02** | **major** unless accepted | U4, U9, U10, U11 (table above) | 16 private declarations in 6 families (10 redundant copies), forced by privacy across files that are mutually foreign. 12 of the 16 are byte-identical within their family. Disclosed (REPORT §7, GF-W1). Under policy §1 *Duplication* and G44-01, disclosure is not acceptance: they need Seyoon's acceptance with a ledger row, or repayment. | **GF-W1.** Recommended: repay with **LE-gf3** at landing (−154/+68). Alternative: DL-61. |
| **GF-F03** | minor | `ModSum.lean:231–237` (F9) | `hSle` composes `Finset.sum_le_sum` with `Finset.sum_const`/`card_univ`/`card_fin`. Mathlib's `Finset.sum_le_card_nsmul` is the one-step form, and its module is already imported. This composes Mathlib lemmas rather than re-proving one, but Codex has flagged near cases. | **LE-gf4**, optional (6 lines). |
| **GF-F04** | minor | `NANDLayering.lean:510–511` (frozen `layerNAND` docstring) | "While N12 and N13 are admitted, `sorryAx` reaches it through them only" is now stale. N12 and N13 are proved, and the trace is empty. Definition docstrings are frozen, so the worker correctly left it and raised GF-W2. | **GF-W2.** Recommended: LE-gf2, with Seyoon's ruling, in U7's landing commit. |
| GF-F05 | info | `NANDLayering.lean` | 947 lines: over the 600 target and over 800, under the 1,000 threshold. The lint shows INFO only. The fold-step case split is proved twice, structurally (N12, before `layerNAND` exists) and semantically. G6A-F06's 800-line split trigger was U8's only. | **GF-W3.** |
| GF-F06 | info | landing | The external head merges cleanly with each moved branch. The in-house `b65668a9` conflicts with #359's LE-g45 in `Combinators.lean` (`const_eval`'s body only), so U8 must rebase onto `d154c883` first. This is in-house, not this delivery. | Landing shape below. |
| GF-F07 | info | REPORT | Every REPORT claim I recounted matches, with three exceptions: the MinMax root note (already in `roots.txt`); GF-F01's omission; and REPORT's U5 Mathlib list (`Nat.pow_log_le_self`), which changes after LE-gf1. | none |
| GF-F08 | info | `NC1.lean:28` | The module sentence names the job ("proved in the fill phase (gsw-6a-fills)"). This is within the permitted sentence, and the base sentence already names the "6a statement phase". | none (optional wording at landing) |
| GF-F09 | info | process | The searches covered TCSlib by name and Mathlib for most helpers. They did not cover Mathlib for inline `have`s (GF-F01). | Future briefs: require a Mathlib shape search for every inline `have` of a general `Nat`/`List`/`Finset` fact. |

## Questions for Seyoon

**GF-W1 (duplicated private helpers; GF-F02).**
- **(A, recommended)** Repay at landing with **LE-gf3**. Since G48-01, the rule has been to fix rather than defer
  when it is cheap, and here it is.
  - A #360 addendum (owner-side, like `cc05f76c`) adds `TreeCircuit.maxDepth_le_of_forall` and
    `TreeCircuit.maxFaninL_le_of_forall` to `Basic.lean`, and `prefixVal_eq_of_false` and `prefixVal_testBit` to
    `Adder.lean`. These are the worker's bodies verbatim.
  - U9's `depth_getD_le` and `maxFanin_getD_le` become public in `CarrySave.lean`.
  - 14 private declarations are deleted. 24 code uses gain a `TreeCircuit.` prefix (2 of them rewrapped); the
    `prefixVal_*`/`*_getD_le` uses resolve unchanged, and docstrings keep the short names. File sizes: BC 533, CarrySave 638, Compare 499, ModSum 416.
  - decls2 then gives +6 public names, all approved by this ruling.
  - Phase 2 replays it. No ledger row is needed, and the `val_eq_prefixVal_*` near pair stays as an info note.
- **(B)** Accept as debt now: a ledger row **DL-61** naming the 16 declarations (and the `val_eq_prefixVal_*` pair), with
  the promotions (REPORT P1–P4) as a post-landing owner-side PR on the dedup queue. The units land as delivered.
- **(C)** Re-issue the four files to the worker after a promotion PR lands. This is slowest, and nothing is gained
  over A.

**GF-W2 (stale frozen `layerNAND` docstring; GF-F04).**
- **(A, recommended)** Approve the frozen-docstring edit **LE-gf2** in U7's landing commit. One sentence becomes
  "N12 and N13 are proved structurally, so no admission reaches it through them." It must land with or after U7,
  because on #359 alone the old sentence is still true.
- **(B)** Leave it for the post-Gate-45 docstring follow-up PR (the LE-g45b kind), filed after U7 lands.
- **(C)** Leave it. Read as a conditional, it is vacuously true. Not recommended.

**GF-W3 (`NANDLayering.lean`, 947 lines; GF-F05).**
- **(A, recommended)** Accept as is. It is under the 1,000 threshold, and policy needs no justification below it.
  Record the size, and require a split if a later change takes it past 1,000.
- **(B)** A later owner-side split: the column invariant into `NANDLayering/Invariant.lean`. That makes about 15
  private lemmas public API.
- **(C)** A compaction re-issue to the worker (one merged invariant, an estimated −100 to −150 lines).

**GF-W4 (new; GF-F01).**
- **(A, recommended)** Apply LE-gf1 at landing without a ledger row (the G48-01 revised-ruling precedent).
- **(B)** Re-issue U5 to the worker.

**GF-W5 (new, optional; GF-F03).**
- **(A, recommended)** Apply LE-gf4 at landing together with LE-gf1.
- **(B)** Leave F9 as is (no duplication of a lemma's proof).

## Proposed landing edits

`landing-edits-proposed.diff` (580 lines). The edits are in order, against the head
`bb7efa82af89141535e7a4adc49c6d97aef85de8`. `Basic.lean` and `Adder.lean` are their blobs there, equal to #360
`cc05f76c`.

| LE | Closes | Files | Size |
|---|---|---|---|
| LE-gf1 | GF-F01 | `NC1.lean` | +5 −8 |
| LE-gf2 | GF-F04 (GF-W2 A) | `NANDLayering.lean` | +3 −2 |
| LE-gf4 | GF-F03 (optional) | `ModSum.lean` | +6 −6 |
| LE-gf3 | GF-F02 (GF-W1 A): 4 promotions, 2 helpers made public, 14 deletions | `Basic.lean`, `Adder.lean`, `BarringtonConverse`, `CarrySave`, `Compare`, `ModSum` | +68 −154 |

Checks made without Lean:
- `git apply` of the combined file onto a copy of the head files reproduces my edited tree exactly.
- The edited files have no line over 100 characters. `Basic.lean`'s three 101–103 lines are pre-existing.
- `style_lint`: 0 findings in the 8 files.
- The promoted bodies are byte-identical to the worker's compiled copies. Their dependencies are core or Mathlib:
  `Nat.le_induction`, `Nat.mod_pow_succ`, `Nat.toNat_testBit`, `max_le`, `List.mem_cons_self`. They are reachable
  from `Basic.lean`'s and `Adder.lean`'s imports.
- LE-gf4's term is the one step I am least sure of without Lean: `rwa … at h`, with `S` a `set` variable. Phase 2
  compiles it. If it fails, drop it; it is optional.

## Merge interaction and landing shape (recommendation only)

`git merge-tree --write-tree` of the head `bb7efa82`:

| With | rc | Tree | Shared paths changed on both sides |
|---|---|---|---|
| #359 `d154c883` (LE-g45/45b: `Combinators`, `Hierarchy`, `Barrington`) | 0 | `4092993e…` | none (the moved `eval_node_nil` is not used by the six files) |
| #360 `cc05f76c` | 0 | `af1db3a3…` | none |
| `fill/gsw-6a-u1-u2` `f31382a5` (Defs, Eval, Barrington) | 0 | `6f71a93b…` | none, beyond identical #359 content |
| `fill/gsw-6a-u8-u6` `b65668a9` (Combinators, NANDForm, TreeDAG) | 0 | `d6a2b6fb…` | none, beyond identical #359 content |
| records tip `2f83708f` | 0 | `70e1e52c…` | none |

The stacked synthetic merge (tip ⊕ `d154c883` ⊕ `cc05f76c` ⊕ `f31382a5` ⊕ head) is clean, and the six files are
blob-equal to the head's.

Adding `b65668a9` conflicts in `Combinators.lean`, only in `const_eval`'s body. The fix is to take #359's
`rw [TreeCircuit.const_eq]; exact eval_node_nil b x`.

**Recommended shape:** one landing branch, replayed and checked as one tree (`workflow.md` §6.1), with
unit-by-unit commits.
1. **#358, then #359 `d154c883`**, after Gate 45 r2 clears.
2. **#360 `cc05f76c`**, plus addendum 2 if GF-W1 = A.
3. **In-house units:** U1–U3 (`f31382a5`), then U8/U6 (`b65668a9`, rebased onto `d154c883`, taking LE-g45's
   `const_eval`).
4. **External units, one commit each, with their LEs:** U4 (commits 3 and 7, plus LE-gf3's U4 part), U5 (with
   LE-gf1), U9, U10, U11 (with LE-gf3 and LE-gf4), and U7 (with LE-gf2).

Order inside step 4: U9 before U10 before U11, and U4 before U5, by imports.

Phase 2 replays that tree on snapshot #6: admissions should then be 74 minus the in-house targets filled, and the
axiom trace of the six owners should shrink to the in-house targets still open. Per-unit PRs are possible, since
every unit touches one file. But U5 needs U4, and U10/U11 need U9, so they would stack anyway. One branch with
per-unit commits is simpler.

## Phase 2 (to do)

Replay on olean snapshot #6:
- the head as delivered and the stacked landing tree, with LE-gf1/2/4 and, if ruled, LE-gf3;
- the sweep of the 9 `DOWN` modules (plus `Basic`/`Adder` downstream if LE-gf3);
- decls2 and the StmtDump of the 41 targets;
- the axioms and trace;
- coe-A canonical seals (A/B/coe-B attributed) for the six owners, plus `Basic`/`Adder` if LE-gf3;
- the liveness pairs and the lint.

Check the four Mathlib imports against the snapshot's package set.

## Evidence

`gsw-6a-fills-final-r1-phase1-evidence.zip`, SHA-256
`aaf8be4f1b684000e12d6ebe6d6a1e9ea1f1577f4d933bb6ae612af1b6253ee9` (38 entries with its internal
`SHA256SUMS`). `evidence-SHA256SUMS` beside it covers the zip and `landing-edits-proposed.diff` (`01c07a11…`).
It contains:
- `tools/`: `decls2.py` (pinned copy), `frozen2.py`, the re-run copy of the worker's `frozen_owned.py`,
  `sorryscan.py`, `tokens.sh`, `rwnames.py`, `sealcount.py`, `sizes.py`, `helpers.py`, `hygiene.py` and `mkle.py`;
- `out/`:
  - integrity, reproduction and diffstat;
  - decls2 (empty = 0/0/0) and the frozen-check outputs;
  - admissions at base and head, and the token counts;
  - `rwnames.tsv`;
  - the seal, liveness and axiom recounts;
  - sizes and hygiene;
  - lint at base and head;
  - the merge-tree log;
  - the helper inventory and `dup-searches.txt`;
- `le/`: the four per-edit diffs.

## Final verdict (phase 2)

**ACCEPT: all checks pass, so the branch was pushed and draft PR #366 opened.** The full record is `phase2.md` beside
this file. The evidence is `gsw-6a-fills-final-r1-phase2-evidence.zip`, SHA-256
`68d89dff5a5fd7d30c0f077be898c046e3f6962d4eb73488b500d5428be482ee`, listed in `evidence-SHA256SUMS`.

### The branch

- `land/gsw-6a-fills` is at `ccca6f804552f72b400c09e7a3bd694371bdf568`, on the records tip `036d8239` (Lean-equal to
  snapshot #6). It has 19 signed first-parent commits:
  - the merges of #358, #359 and #360;
  - #360 addendum 2 (LE-gf3 part 1, the four promotions);
  - the in-house U1/U2, U3, U8 and U6 as content commits (U8 keeps LE-g45's `const_eval`);
  - the 7 worker commits, cherry-picked with `-S` (range-diff 7/7 `=`; the patches reproduce `bb7efa82`);
  - LE-gf1, LE-gf3 part 2, LE-gf2 and LE-gf4.
- All four landing edits landed. **LE-gf4 compiles and is kept.** The edited files equal `bb7efa82` with the recorded
  diff applied.

### Replay on snapshot #6

- 564 downstream modules were built: rc 0, 0 errors.
- State check: RESULT OK over 1445 modules. Link count 1 for all 564 rebuilt modules.
- Snapshot #6 rehash: 0/0/0 at the start, after the build and at the end.

### Admissions

- 0 in the 13 6a modules.
- 192 in 44 modules library-wide, equal module by module to #6 (the build's per-module `sorry` warnings agree).

### Axioms

- All 98 targets are standard.
- 859 census constants: none non-standard, and no `sorryAx` trace.
- `layerNAND`, `layerNAND_gates`, `layerNAND_output` and `toNANDForm` are standard.

### decls2 against the tip

- 289 ADDED: #358/#359 268, #360 15, and the 6 LE-gf3 public names.
- 1 REMOVED: the `eval_node_nil` move.
- 0 CHANGED. LE-gf2 is a docstring change, so decls2 does not track it.

### Rule 10

- coe-A on 22 owners: 0 errors in the 6a owners. The failures are only the pre-existing ones, with identical
  declarations (Adder 3, DAGTransform 11, TreeDAG 25, TreeNCAC 2, Hierarchy 2).
- Root: 14,098 requests, 0 errors.
- Paired controls for the 6 public lemmas: ALL_OK (attempt 2; attempt 1 had a control-statement defect and is kept).
- Explicit-unfold scan: 0 new foreign unfolds against the tip.

### Lint, duplication and disk

- Lint: no new FAIL or WARN.
- The duplication sweep of the 6 public lemmas and the 75 remaining private helpers finds no duplicate.
- To keep the disk margin, `olean-replay-6a-fill12`, `-6a-fill86` and `-6a-readers` were deleted.

### Disclosed

- The stale frozen in-house docstrings (Defs, Eval and Barrington module text; NANDForm on N2) are left for a docstring
  follow-up.
- `NANDLayering` is 948 lines.
- LE-gf3's real size is +72/−168, not the +68/−154 this review stated.
- **The tip moved.** #347/#355 merged during the run (tip `acd66709`).
  - The merge-tree is clean, but 3 tip-changed modules are in the rebuilt set.
  - The coordinator's rebase request arrived after the build and the seals were complete, so the branch was finished
    on #6 as instructed.
  - Before merge, the branch must be rebased onto the new tip and re-replayed on snapshot #7.
  - `olean-replay-6a-land` is not adoptable.
