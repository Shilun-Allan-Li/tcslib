# gsw-6a-statements · checkpoint 1 review (maintainer, static)

**Verdict: PROCEED WITH NOTES.** 0 blockers, 0 majors, 2 minors (G6A-C1-F01, F02), 6 infos. O1 is complete and
correct at checkpoint scope; the statement files were not delivered at this checkpoint, so their review is carried
by the final (which arrived during this review: exchange `d7a9adb5b70c70c1b6fb8dc3d0aa5a60d720c1ef`, reviewed in
`final-6a-r1/review.md`). This file is kept short, as the final supersedes everything except O1.

## Delivery
- Exchange `c0e11b31fd0146de79b3af48fede99714376d682` ("stmt gsw-6a: checkpoint 1", 2026-11-16 21:42, unsigned),
  parent `443df15b`; it touches only `inbox/fills/gsw-6a-statements/`. Extracted with `git archive` into an empty
  scratch directory.
- Contents: `REPORT.md`, `patches/o1/` (1 commit), `src-o1/` (4 files), `evidence/` (169 files), `SHA256SUMS`.
  No `patches/stmt/` and no `src/` (G6A-C1-F01).
- Contract: `issued-6a-r1/SHA256SUMS` 7/7 OK; plan section r3 `06824b3d…` and rulings `312fef45…` equal at the
  records pin `c5eb7cf4` and in the pack's `inputs/`; the pack at `7031cef6` is byte-equal to the records folder.

## Checks
- **Integrity.** Top-level `SHA256SUMS` 177/177 and `evidence/SHA256SUMS` 169/169 verify; the delivered path sets
  equal the manifests exactly (no extra, none missing, no `./`).
- **Reproduction.** `git am` on the issue base `f6f295a6` with `COMMITS.tsv`'s committer data and no signing
  reproduces `413e9aa42f6b96b4d65673c37c83819b2fb77579`; `src-o1/` equals the four changed files byte for byte;
  signing column `none`, commit unsigned; authorship of the moved code (`Authors: Hydroxyi`) kept.
- **decls2** (maintainer copy, run in the reproduced worktree): exactly 7 ADDED (`TreeCircuit.balanced`,
  `balanced_eval`, `maxFanin_balanced_le`, `depth_balanced_le`, `size_balanced_le`, `balanced_nil`,
  `balanced_singleton`), 0 CHANGED, 0 REMOVED; equal to the delivered `decls2.tsv` and to r3 §H5.8. (The removed
  `combine*` were private, so decls2 does not list them.)
- **O1 content.** My own comparison of base `TreeNCAC.lean:172–350` (renamed) against `Combinators.lean:44–244`
  shows exactly: the three named repairs (`:195`, `:199`, `:261` → `eval_node_true`/`_false`, with
  `List.all_cons`/`any_cons` for `foldr_cons`), two further nil-case repairs (G6A-C1-F02), three whitespace re-wraps of
  base lines over 100, the five promoted docstrings and the two new `rfl` readers. `TreeNCAC.lean`: one import, the
  removed block, `toBinary`'s body and four proof lines re-pointed; statements unchanged (frozen check 0 violations,
  both controls behave).
- **Statements (O1).** The seven headers equal r3 §H5.8. Each public lemma has a formula docstring. No target in O1,
  so no sketch is required; the only moved proof over ~20 lines (`combineFuel_depth`) keeps its sketch.
- **Axioms.** 141 constants of `Combinators`, `FormulaArith`, `TreeNCAC`: only `propext`/`Classical.choice`/
  `Quot.sound` or none; no `sorryAx`, empty trace.
- **Rule 10.** Seals A/B/coe-A/coe-B: `Combinators` 174 requests, `FormulaArith` 194, 0 errors in all four;
  `TreeNCAC` 194, 2 errors in all four (G6A-C1-F03). Controls on `balanced`: unsealed 0, sealed exactly 1,
  positive 0. Unfold scan: 0 foreign in `Combinators`; 4 pre-existing in `TreeNCAC` (`:188`, `:228`, `:250`, `:268`).
- **Builds.** Closure at the O1 head: 8 modules rc 0, 0 errors in both forms, 0 `sorry`; the logged source hash of
  `TreeNCAC` (`41ebf40a…`) equals the reproduced blob.
- **Placement and size.** All under `Complexity/CircuitComplexity/`. `Combinators` 246 lines (width ≤ 99),
  facade 23, `TreeNCAC` 537 → 359; its remaining lines over 100 (`:62`, `:165`) and `@[simp]` at `:108` are
  pre-existing. Lint line sets equal (25 FAIL / 390 WARN, 500 → 502 files); `style_lint` 0 findings.
- **Clash and reuse.** No new name, public or private, is declared elsewhere in `TCSlib/` at the base or at the tip
  `465343dd`; no other balanced-tree construction on `TreeCircuit` exists. No duplicate is left behind.
- **Sources.** Only the existing [AB09, p. 118] tag of `toBinary`, kept; no new tag, no [Gen09].
- **Freshness.** The tip `465343dd` is Lean-equal to `463f2244` (#351, #352). Since the base, only `TCSlib.lean`
  (#331, Cryptography block) and `Uniform.lean` (#341) changed among 6a-relevant paths; neither is an O1 path. The
  downstream of `TreeNCAC` and the facade is the same 6 modules plus the root at the base and the tip.
  `git merge-tree` tip × `413e9aa4` is clean (tree `dd67292e…`), all four O1 files blob-equal. Open PRs #340, #346,
  #347, #350 touch none of the 6a paths.
- **Statement progress (unverifiable here).** The closure log at an unnamed statement head shows all 13 new modules
  rc 0, with 100 `sorry` warnings (Defs 11, Eval 5, Barrington 11, BarringtonConverse 11, NC1 5, NANDForm 6,
  NANDLayering 7, Combinators 26, CarrySave 7, Compare 7, ModSum 4). Probes P8 and P9 pass by kernel `decide`;
  P8's gate counts and depths equal r3 §H3.9's table, and P9 checks N7–N11 on three instances including the real
  `layerNAND`, plus the odd-gap (XOR non-monotonicity) finding.

## Findings

| # | Severity | Finding | Disposition |
|---|---|---|---|
| G6A-C1-F01 | minor, process | No `patches/stmt/` or `src/`: the claim that Defs, Eval and NANDForm compile rests on logs with source hashes only, and no statement could be reviewed at checkpoint 1. The brief's delivery list reads as applying to every checkpoint; its checkpoint definition names only O1's series. | Superseded by the final. For future briefs: say explicitly that each checkpoint carries `src/` of every file it claims compiled, and the head hash. |
| G6A-C1-F02 | minor, disclosed deviation | Two repairs beyond the brief's "byte-identical except three": `sumSize_pairUp` and `maxFaninL_pairUp`, nil case, now read `sumSize []`/`maxFaninL []` through the `rfl` readers `sumSize_nil`/`maxFaninL_nil` (`Basic.lean:235/242`) instead of by definitional unfolding. Without them the new owner fails its seal, which r3 §H8 item 20 requires to pass; r3 §H2 missed these two reads. Semantics-free. | **Seyoon to ratify** (Q-C1 below). Recommended: accept. |
| G6A-C1-F03 | info, pre-existing | `TreeNCAC.lean` still fails its seal twice, in the byte-identical private `maxDepth_map_le`/`maxFaninL_map_le` (`| [], _ => Nat.zero_le _`, `:195`, `:206`); at the base the file had these two plus the two now repaired. Its four explicit foreign unfolds are also pre-existing. | Add both reads and the `hlit` unfolds to clean-up part 2 beside the recorded line-366 read. No action in O1. |
| G6A-C1-F04 | info | `REPORT.md` does not name the `stmt/gsw-6a` commit behind the closure run; the per-module source hashes in `final-closure/summary.txt` are the only binding. | Cross-checked against the final in `final-6a-r1/review.md`. |
| G6A-C1-F05 | info, docstring | `Combinators.lean`'s module docstring says the gate was "promoted unchanged" (five repairs were made) and points to a registry subsection that exists only after the statement series. | Harmless if O1 and the statement PR land together; otherwise a one-word fix. |
| G6A-C1-F06 | info | `TreeNCAC` now imports `TreeDAG` and `DAGCircuit` through `Combinators`, so a future `DAGCircuit.lean` change rebuilds the `TreeNCAC` chain. The brief foresaw the import (no cycle). | Record only. |
| G6A-C1-F07 | info, nits | REPORT says the pack's `SHA256SUMS` has 6 files (it has 7); sub-agent logs are deferred to the final; P9 labels `oddC` an "odd gap of 3", but the padding there is even (a double-NAND chain) and the parity twins are exercised by `xorC` and `zeroC`. | None at checkpoint; check P9's wording against `NANDLayering`'s docstrings in the final. |
| G6A-C1-F08 | info, size watch | `Combinators.lean` holds 26 targets between lines 303 and 655 at the statement head; with r3's U8 estimate of 150–220 fill lines it would fill to about 800–900 lines, under the 1000 cap but over the 600 target. | Checked in the final review. |

## Questions for Seyoon
- **Q-C1 (G6A-C1-F02), the two extra O1 repairs.**
  - **A (rec.)** Accept the five-repair form: the brief's intent (the new owner passes its seal, nothing duplicated)
    is met, and the extra hunks only replace definitional reads by published `rfl` readers.
  - **B** Restore the brief's three-repair form and grant `Combinators.lean` a seal exception for the two nil cases.

Out of scope here: bootstrapping and circular security are 6b (Gate 46) and are not in this job; nothing under
`Cryptography/` was delivered, and no [Gen09] is cited.

Final delivery: arrived (`d7a9adb5b`, 2026-11-17 05:09); see `final-6a-r1/review.md`.
