The **GSW phase 6a statements** (plan r3 §H5, rulings P6-Q1..Q19): branching programs and both directions of Barrington's theorem, the NC¹ corollary, the DAG-to-NAND conversion and its layering, and the formula-arithmetic layer, all under `Complexity/`. This PR has statements only: **98 targets are `sorry`**, each with its row marker, deviations and a **Proof sketch**. Every definition and reader is proved.

**Stacked on PR O1** (#358, `land/gsw-6a-o1`, `a616adca`). Until O1 merges, the base of this PR is `land/gsw-6a-o1`; after it merges, retarget to `cryptography/pass-shelat-ch2-4`.

**Head:** `73aedcdaaaffef7e69ab012d9b9195f150bae68d` (tree `2c243bb1`). It was re-cut onto the records tip `e1d39836` after #340 and #346 merged (phase 2's head was `66036926`; range-diff 6/6 `=`, and every commit's tree equals `git merge-tree` of the tip and the old commit). Six commits:
- five maintainer-signed cherry-picks of the worker's `ad8e170f..ec36703b` (delivery at exchange `d7a9adb5`): `453fb1ab` (Defs, Eval), `c4870dd3` (Barrington, BarringtonConverse, NC1, facade), `d8d0cf95` (NANDForm, NANDLayering), `06b7734a` (FormulaArith), `d7a72780` (registrations, registry rows H18–H20);
- **`73aedcda`, landing edit LE-ren** (review G6A-F01; 6a Q1 ruled A). `TreeCircuit.rename` restated the public, proved `TreeCircuit.reidx` (`BooleanAnalysis/LMN/CircuitReindex.lean`), and `rename_eval`/`depth_rename` restated `reidx_eval`/`reidx_depth`. LE-ren drops `rename`, `rename_eq`, `rename_eval` and `depth_rename`, and points the module docstring, the facade contents and the registry row to `reidx`. Admissions 100 → 98; `Combinators.lean` 659 → 629 lines. The fourth commit's message still lists `rename`; LE-ren supersedes it.

## Files (17 against PR O1)
- `Complexity/BranchingPrograms.lean` and `BranchingPrograms/{Defs, Eval, Barrington, BarringtonConverse, NC1}.lean` (new);
- `CircuitComplexity/{NANDForm, NANDLayering}.lean` (new);
- `CircuitComplexity/FormulaArith/{CarrySave, Compare, ModSum}.lean` (new); `Combinators.lean` (F1–F3 appended to O1's file) and the `FormulaArith.lean` facade;
- `CircuitComplexity.lean` and `ComputationalModels.lean` (registrations), `TCSlib.lean` (one import), and `machine-library-design.md` (§14 status, rows H18–H20, "Circuit and formula gadgets").

## Checks (maintainer, this head on the tip, from the O1 replay on olean snapshot #5; `briefs/lattice-gsw/phase6/final-6a-r1/phase2.md`, R2 and "Re-replay on snapshot #5")
- **Range-diff:** 5/5 identical to the delivered series; LE-ren is byte-identical to the review's proposed diff, and nothing references `rename` afterwards.
- **Build** (re-replay on snapshot #5, T `3f540c22`): 20/20 modules rebuild with rc 0 and 0 errors; the state check gives 1440/1440 (1435 on #4, plus the 5 modules #340/#346 added). The only warnings are the 98 `sorry` lines.
- **Admissions:** **+98** against the tip, exactly the 98 targets (Defs 11, Eval 5, Barrington 11, BarringtonConverse 11, NC1 5, NANDForm 6, NANDLayering 7, Combinators 24, CarrySave 7, Compare 7, ModSum 4); unchanged from #4.
- **Axioms:** 544 constants, no axiom beyond the standard three and `sorryAx`. `sorryAx` is in exactly the 98 targets and five definitions: `toNANDForm`, `toNANDForm_eq` (through N2 only) and `layerNAND`, `layerNAND_gates`, `layerNAND_output` (through N12–N13 only). The probe log is byte-identical to the #4 run.
- **Rule 10:**
  - canonical coe-A seals of the 16 new or changed files, re-run on #5 (facades chunked): 0 errors, except `TreeNCAC`'s two pre-existing failures (G6A-F05, identical at the tip); request sets and outcomes equal the #4 run, which equal the delivery's minus `rename`;
  - root coe-A, re-run on #5: 14,074 requests in 15 chunks, 0 errors (13,991 on #4; the 83 added names all live in #340's and #346's files);
  - the strict A/B and coe-B seals, the paired controls (ALL_OK in both harnesses, 92 sealed negatives each), the delivery's 30 paired controls (30/30) and the explicit-unfold scan (0 foreign unfolds in the 13 new files) are carried forward from #4: every non-root owner's import closure is byte-identical at both heads (equal closure keys), and the coe-A re-run reproduces the #4 request sets and probes.
- **Lint:** the FAIL/WARN line sets equal the tip's; `style_lint` gives 0 findings in the 13 new files (both byte-identical to #4); every file is under 1,000 lines and only `Combinators` (629) is above the 600 target (G6A-F06: split at the fill if it passes 800).
- **Clashes** (re-run at the tip `e1d39836`, which has #340's and #346's names): 281 new names, 0 clashes (11 share a name with O1's private moves out of `TreeNCAC`, whose tip copies O1 removes).
- **#340 and #346** are merged into the base; neither shares a file with this PR or a module with its closure except the import-only root.

## Review, rulings and merge order
- **Verdict:** **ACCEPT** with LE-ren (`briefs/lattice-gsw/phase6/final-6a-r1/review.md`, phases 1 and 2). Rulings 6a Q1–Q4 (Seyoon): LE-ren applied; O1's five repairs accepted; the owner-side reader PR (nine readers and `gadgetCorrect_iff`) comes separately, before the fills; N12 stays in the `args_lt` field form.
- **Gate:** **Gate 45 (Codex) audits both** this PR and PR O1 (#358).
- **Merge order:** after PR O1. If it follows O1 directly, the replay output `olean-replay-6a-stmt` is adopted as the next snapshot when the merge commit's Lean paths equal tree `2c243bb1`; otherwise its 20 modules re-replay on the new tip.

---
_Generated by [Claude Code](https://claude.ai/code/session_01PqpVTiuDcjSqhyfbqnsVxA)_