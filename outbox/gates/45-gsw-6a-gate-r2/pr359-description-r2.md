The **GSW phase 6a statements** (plan r3 §H5, rulings P6-Q1..Q19): branching programs and both directions of Barrington's theorem, the NC¹ corollary, the DAG-to-NAND conversion and its layering, and the formula-arithmetic layer, all under `Complexity/`. This PR has statements only: **97 targets are `sorry`**, each with its row marker, deviations and a **Proof sketch**. Every definition and reader is proved.

**Stacked on PR O1** (#358, `land/gsw-6a-o1`, `a616adca`). Until O1 merges, the base of this PR is `land/gsw-6a-o1`; after it merges, retarget to `cryptography/pass-shelat-ch2-4`.

**Head:** `d154c8830fc8ffc52671b41992e7dbef61e30959` (tree `be58919e`). The series was re-cut onto the records tip `e1d39836` after #340 and #346 merged (phase 2's head was `66036926`; range-diff 6/6 `=`, and every commit's tree equals `git merge-tree` of the tip and the old commit). Gate 45's two landing edits follow. Eight commits:
- five maintainer-signed cherry-picks of the worker's `ad8e170f..ec36703b` (delivery at exchange `d7a9adb5`): `453fb1ab` (Defs, Eval), `c4870dd3` (Barrington, BarringtonConverse, NC1, facade), `d8d0cf95` (NANDForm, NANDLayering), `06b7734a` (FormulaArith), `d7a72780` (registrations, registry rows H18–H20);
- **`73aedcda`, landing edit LE-ren** (review G6A-F01; 6a Q1 ruled A). `TreeCircuit.rename` restated the public, proved `TreeCircuit.reidx` (`BooleanAnalysis/LMN/CircuitReindex.lean`), and `rename_eval`/`depth_rename` restated `reidx_eval`/`reidx_depth`. LE-ren drops `rename`, `rename_eq`, `rename_eval` and `depth_rename`, and points the module docstring, the facade contents and the registry row to `reidx`. Admissions 100 → 98; `Combinators.lean` 659 → 629 lines. The fourth commit's message still lists `rename`; LE-ren supersedes it.
- **`ad9c4fc7`, landing edit LE-g45** (Gate 45 G45-01..03; Seyoon ruled: fix now). 3 files, +15/−14:
  - **G45-01:** `BoolCircuit.eval_node_nil` moves from `CircuitComplexity/Hierarchy.lean` into `FormulaArith/Combinators.lean` (just before `TreeCircuit.const`) with the same name, binders, statement and docstring. Its proof now reads `TreeDAG`'s `eval_node_true`/`eval_node_false` instead of unfolding `Basic`'s `TreeCircuit.eval` (Rule 10). `Hierarchy` reaches `Combinators` through `TreeNCAC`, so its two users still resolve. The F3 target `TreeCircuit.const_eval` becomes the proved citation `rw [TreeCircuit.const_eq]; exact eval_node_nil b x`, statement unchanged. **Admissions 98 → 97.**
  - **G45-03:** Barrington's convention note and C9 docstring call `(13254)` Bar89's one-based cycle notation, whose zero-based form `(0 2 1 4 3)` is what the code implements. Prose only.
  - **G45-02:** `Combinators`' module docstring says the promoted `combine` keeps its computation unchanged and its proofs carry the five Q2-approved Rule 10 repairs. Prose only.
- **`d154c883`, landing edit LE-g45b** (docstring follow-up to LE-g45). 2 files, +13/−7, comments and docstrings only:
  - `Barrington.lean`: the module docstring's `sigma1`/`sigma2` entry and the `sigma1`/`sigma2` docstrings no longer call Bar89's `(12345)`/`(13542)` "0-based". Like LE-g45's wording, they call it Bar89's one-based cycle notation, implemented in zero-based form as `(0 1 2 3 4)`/`(0 2 4 3 1)`. These were the last "0-based"/"zero-based"/"one-based" phrasings in `BranchingPrograms/` that needed a fix. BV14's "1-based state" at C16 is accurate and unchanged.
  - `Combinators.lean`: `## Main results` lists `const_eval` as proved from `BoolCircuit.eval_node_nil` (now homed in this file) and drops it from the "(F3; targets)" entry.
  - The comment-stripped code of both files (nested block comments, doc comments and line comments removed; string and char literals kept) is byte-identical to `ad9c4fc7`. Three code mutations per file (a space after the first `:=`, one code token changed, one code line commented out) are each caught. A docstring-only mutation stays equal.

## Files (18 against PR O1)
- `Complexity/BranchingPrograms.lean` and `BranchingPrograms/{Defs, Eval, Barrington, BarringtonConverse, NC1}.lean` (new);
- `CircuitComplexity/{NANDForm, NANDLayering}.lean` (new);
- `CircuitComplexity/FormulaArith/{CarrySave, Compare, ModSum}.lean` (new); `Combinators.lean` (F1–F3 appended to O1's file, and LE-g45's `eval_node_nil`) and the `FormulaArith.lean` facade;
- `CircuitComplexity/Hierarchy.lean` (LE-g45: `eval_node_nil` moved out);
- `CircuitComplexity.lean` and `ComputationalModels.lean` (registrations), `TCSlib.lean` (one import), and `machine-library-design.md` (§14 status, rows H18–H20, "Circuit and formula gadgets").

## Checks
Maintainer checks of `73aedcda` on the tip, from the O1 replay on olean snapshot #5, are in `briefs/lattice-gsw/phase6/final-6a-r1/phase2.md` (R2 and "Re-replay on snapshot #5"). The LE-g45 and LE-g45b checks are in `briefs/lattice-gsw/gates/45-gsw-6a/le-g45.md` and `le-g45b.md`.
- **Range-diff:** 5/5 identical to the delivered series; LE-ren is byte-identical to the review's proposed diff, and nothing references `rename` afterwards.
- **Build:**
  - At `73aedcda` (re-replay on snapshot #5, T `3f540c22`): 20/20 modules rebuild with rc 0 and 0 errors. The state check gives 1440/1440 (1435 on #4, plus the 5 modules #340/#346 added).
  - LE-g45 and LE-g45b each rebuild the same 16 downstream modules on the previous replay tree with rc 0 and 0 errors. The state check gives 1440/1440 OK at each head. The only warnings are the 97 `sorry` lines.
  - LE-g45b's warnings equal LE-g45's: 14 modules are SAME, and the two edited files match after their +3 line shift.
- **Admissions:** **+97** against the tip, exactly the 97 targets (Defs 11, Eval 5, Barrington 11, BarringtonConverse 11, NC1 5, NANDForm 6, NANDLayering 7, Combinators 23, CarrySave 7, Compare 7, ModSum 4). The exact-target check against the delivered row map minus `rename_eval`, `depth_rename` and `const_eval` gives RESULT EXACT. LE-g45b's admitted (file, name) set equals LE-g45's.
- **Axioms:** 545 constants, no axiom beyond the standard three and `sorryAx`.
  - `sorryAx` is in exactly the 97 targets and five dependents, two definitions and three theorems: `toNANDForm`, `toNANDForm_eq` (through N2 only) and `layerNAND`, `layerNAND_gates`, `layerNAND_output` (through N12–N13 only).
  - `eval_node_nil` and `const_eval` use `[propext, Classical.choice, Quot.sound]`.
  - At LE-g45b, both axiom probe logs are byte-identical to LE-g45's.
- **Rule 10:**
  - canonical coe-A seals of the 16 new or changed files, re-run on #5 (facades chunked): 0 errors, except `TreeNCAC`'s two pre-existing failures (G6A-F05, identical at the tip); request sets and outcomes equal the #4 run, which equal the delivery's minus `rename`;
  - LE-g45 and LE-g45b, canonical coe-A at each head:
    - `Combinators`: 174 requests, 0 errors.
    - `Barrington`: 119 requests, 0 errors.
    - `Hierarchy` (LE-g45): 355 requests, with 2 errors in `Language.InTreeSize.inSIZE`. The same 2 errors occur at `73aedcda`, so they are pre-existing.
    - Request sets are equal across the heads.
    - LE-g45's explicit-unfold scan finds 0 new foreign unfolds and removes one (the old `simp [TreeCircuit.eval]`).
  - root coe-A, re-run on #5: 14,074 requests in 15 chunks, 0 errors (13,991 on #4; the 83 added names all live in #340's and #346's files);
  - the strict A/B and coe-B seals, the paired controls (ALL_OK in both harnesses, 92 sealed negatives each), the delivery's 30 paired controls (30/30) and the explicit-unfold scan (0 foreign unfolds in the 13 new files) are carried forward from #4: every non-root owner's import closure is byte-identical at both heads (equal closure keys), and the coe-A re-run reproduces the #4 request sets and probes.
- **Lint:**
  - The FAIL/WARN line sets equal the tip's. LE-g45 and LE-g45b change only the INFO line counts.
  - `style_lint` gives 0 findings in the 13 new files. Its two `Hierarchy:17` findings ("theorem below" in a docstring) are pre-existing.
  - Every file is under 1,000 lines. Only `Combinators` (636) is above the 600 target (G6A-F06: split at the fill if it passes 800).
- **Clashes** (re-run at the tip `e1d39836`, which has #340's and #346's names): 281 new names, 0 clashes (11 share a name with O1's private moves out of `TreeNCAC`, whose tip copies O1 removes).
- **#340 and #346** are merged into the base; neither shares a file with this PR or a module with its closure except the import-only root.

## Review, gate, rulings and merge order
- **Verdict:** **ACCEPT** with LE-ren (`briefs/lattice-gsw/phase6/final-6a-r1/review.md`, phases 1 and 2). Rulings 6a Q1–Q4 (Seyoon): LE-ren applied; O1's five repairs accepted; the owner-side reader PR (nine readers and `gadgetCorrect_iff`) comes separately, before the fills; N12 stays in the `args_lt` field form.
- **Gate 45 (Codex), round 1** (`briefs/lattice-gsw/gates/45-gsw-6a/findings-r1.md`, at `73aedcda`):
  - **#358 CLEAR.** **#359 HOLD** on G45-01 (Major): `const_eval` exactly restated the proved `eval_node_nil`. LE-g45 fixes this.
  - G45-02 (Note, inherited from #358) and G45-03 (Minor) are fixed by LE-g45. LE-g45b completes G45-03's wording in the remaining Barrington docstrings.
  - Every other surface passed: all 98 targets as audited, now 97, are sound as stated.
- **Merge order:** after PR O1. If it follows O1 directly, the replay output `olean-replay-6a-stmt-g45b` is adopted as the next snapshot when the merge commit's Lean paths equal tree `be58919e`. Its output map, with Mathlib excluded, has 1471 entries and SHA-256 `fa2067748de73f7fd1d0645ed17e5a5163f365a9556a2155d37910f5817d904c`. Otherwise its modules re-replay on the new tip.

🤖 Generated with [Claude Code](https://claude.com/claude-code)

https://claude.ai/code/session_01PqpVTiuDcjSqhyfbqnsVxA