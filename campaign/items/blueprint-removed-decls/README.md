# Blueprint entries for declarations the campaign removed (2026-11-17)

Found while preparing gate 159 (the W7 integration audit). The W5 blueprint pass and #362
missed these entries: the dependency graph W5 rebuilt kept old entries for modules outside the
snapshot, so the validator did not report the FormulaKit labels as orphans.

**How they were found** (`removed.py.txt`, `REMOVED-STILL-NAMED.json`):
- `declfreeze`'s parser lists every declaration in the 217 Lean files the campaign changed
  against `main`, at `main` and at the campaign tip.
- **654 declarations** are on `main` but on no changed file at the tip.
- A Lean probe against `oleans-cc91f4` confirms that none of the 654 exists in the 898-module
  build (`TOTAL|654|0`).
- `STALE-ENTRIES.json` lists the blueprint entries and `\uses` that still name them.

**Repaired here** (Seyoon, 2026-11-17: "Repair first"):

| Entry | Was | Now |
|---|---|---|
| `Complexity/FormulaKit/Emit.tex`, `Gate.tex` (39 entries) | chapters for FormulaKit, removed by W2 (#328) | deleted, with their two lines in `organization.json` and the `formulas.tex` wrapper |
| `Randomized.PolyAmp.two_pow_bits_le` | entry in SpaceAmplifyPoly | retargeted to `Complexity.LogProg.two_pow_bits_le_two_mul_add_one` (NatBits), the same statement `2^{\|bits n\|} ≤ 2n + 1`; its `\uses` follow |
| `Randomized.PolyAmp.lt_two_pow_bits` | entry in SpaceAmplifyPoly | retargeted to `Complexity.LogProg.lt_two_pow_bits` (NatBits), the same statement; 3 `\uses` follow |
| `Randomized.BPLInP.coreSum_eq_of_code_eq` | entry in BPLInPCount | deleted, a duplicate of `Complexity.ExpBFS.coreSum_eq_of_code_eq` (identical statement, already documented in ExpBFS/Radius); 5 `\uses` repointed |
| `Turing.runFrom_one` | entry in EmitIterEmbed | retargeted to `Turing.MultiTapeTM.runFrom_one` (RO-1's public lemma, for any symbol and state types); the prose is widened to match; 1 `\uses` follows |

The `formulas.tex` wrapper was edited by hand. `scripts/blueprint_assemble.py` stops on the
external FABL dataset, which is not available here. The wrapper now lists exactly the chapter's
`organization.json` modules.

**Validation** (`scripts/blueprint_validate.py` from the repository root, with W5's refreshed
`dep_graph.json` swapped in and then restored):
- **before:** 29,096 labels, 860 orphans;
- **after:** 29,056 labels, 856 orphans;
- both: 0 dangling `\uses`, 0 duplicate bindings, 0 `\uses` cycles.

The four fewer orphans are the four non-FormulaKit entries above. They were among the 860 that
gate 157 classified as never compiled; that classification was off by these four.

**Not repaired: generated dataset content.** Two kinds of text are produced by `main`'s
dataset pipeline (`scripts/dataset_pipeline.py`), not by blueprint writers, and still name
removed declarations:
- `blueprint/src/references/statements` (567 names) and `references/informalized` (386);
- the `\proofstep{…}` annotations in 11 chapters (about 300 occurrences, for example in
  Randomized/ZeroPPIT and PolyHierarchy/Collapse).

They lag the Lean, and a dataset rebuild after the integration refreshes them. That rebuild
needs the external FABL dataset project.
