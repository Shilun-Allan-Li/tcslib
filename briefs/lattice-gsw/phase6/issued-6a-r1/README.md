# Claude statement job `gsw-6a-statements` (GSW phase 6a statements, and owner PR O1)

Claude is the worker, a lead with up to 2 sub-agents (Seyoon's ruling of 2026-11-16: the 6a statements go to an
external Claude session that Seyoon dispatches; `PassShelatChapter5-8Plan.md`). The job writes the statement phase of
phase 6a from plan section r3 (`../plan-section.md`): the branching-program model and host, Barrington's Theorems 1
and 2 with the class corollaries, the NAND conversion, the layering conversion (P6-Q14 B) and the formula-arithmetic
layer, all under `Complexity/`, with their registrations and the §14 rows H18–H20. O1 (`TreeNCAC.combine` promoted as
`TreeCircuit.balanced`, proved) is a separate small series on its own branch. Nothing of 6b; O2 is not in it; nothing
depends on Gen09. Gate 45 (Codex) audits the delivery.

**Base.** `f6f295a6502b72bbf498bb8c64b63f847e910866`, the records tip at issue (fetched by name). Its Lean is the
merged #327/#324 state: the last commit touching a `.lean` file is #324's merge
`201bf57a941131d1737295089ffd7477e1d7f7b9`, and no `.lean` file changed from `99eae2c1` (r2's line references) to
the base.

**Open PRs.** 6a edits only new files under `Complexity/`, `TreeNCAC.lean`, the facade `CircuitComplexity.lean`,
`ComputationalModels.lean`, `TCSlib.lean` and `machine-library-design.md`, so it is path-disjoint from #331 (pairing
statements), #338 and #339 (GSW fills), #340 (on #331) and #341 (sc-yao), except for `TCSlib.lean`, which #331 also
edits in a different hunk (its Cryptography block; 6a's import goes in the Complexity block). #341 changes
`Complexity/CircuitComplexity/Uniform.lean`, which 6a neither edits nor imports. Checked against the PRs' file lists
at issue.

Read [the brief](brief.md) and the [environment addendum](fill-environment-addendum.md) (v1 with an adaptation for
this job). Verify the package with `shasum -a 256 -c SHA256SUMS` from this directory.

- [Build order](order.txt): the 1,340 modules reachable from `TCSlib.lean` at the base, in import order (a
  depth-first post-order, imports in file order), root last. Modules 1–10 are the upstream closure of the existing
  modules the new files may import (`Basic`, `DAGCircuit`, `TreeDAG`, `DAGTransform`, `DAGFanin`, `TreeNCAC`, `NCAC`,
  `Adder`); module 205 is the facade `CircuitComplexity`, module 214 `ComputationalModels`. 34 files under `TCSlib/`
  are not reachable from the root and are not listed.
- [Mathlib roots](roots.txt): 377, the Mathlib modules the listed modules import directly.
- [Source hashes](SOURCE-SHA256SUMS) of the 1,340 files at the base, read from the git objects.
- [Base admissions](base-sorries.txt): 229 declarations in 52 modules, from a syntactic scan (comments and strings
  stripped, `sorry` tokens attributed to the enclosing declaration); none under `CircuitComplexity/`. The final
  must add exactly the new targets; the root build's warnings are the check.
- The exchange pack adds `inputs/` (with its own `SHA256SUMS`): the r3 plan section, `rulings.md` and the Bar89
  ingest (`.md`, `.raw.md`), byte-identical to the records and the base.

Claude returns at least one checkpoint and the final only at `inbox/fills/gsw-6a-statements/` on the exchange; it
never pushes a campaign branch. Seyoon dispatches with the prompt in the records' `dispatch.md` (beside this file
in `briefs/lattice-gsw/phase6/issued-6a-r1/`; it is not part of the pack).

**Size** (maintainer's assessment). About 1,600–2,100 statement lines in 11 math files and 2 facades, O1 (about 180
lines moved), and the full evidence of a statement phase. One job is right: the lead and two sub-agents work on
disjoint files (branching programs; formula arithmetic; O1, NAND form, layering and registrations), and the one
internal dependency (`BarringtonConverse` on O1's `balanced`) is ordered by checkpoint 1. The long step is the root
build (1,340 modules, one Lean process at a time); the addendum lets the final mark it incomplete rather than fail.
If the job must be split (for example if checkpoint 1 slips), split it at checkpoint 1:
- **6a-1, circuits**: O1; `FormulaArith/{Combinators,CarrySave,Compare,ModSum}` and its facade; `NANDForm`,
  `NANDLayering`; the `CircuitComplexity` facade; the conversions `toNANDForm`, `layerNAND`; rows H19, H20 and the
  gadget subsection; probes P8–P10.
- **6a-2, branching programs**, stacked on 6a-1's O1 head (it needs `balanced`): `BranchingPrograms/` and its facade;
  the model and conversions `barrington`, `toFormula`; the `TCSlib.lean` import; row H18; probes P1–P7; the root
  build.

Both halves would use this brief, each restricted to its files, with its own inbox path.

**Maintainer steps before dispatch:** commit this folder and the r3 plan section to the records (the plan section
byte-identical to `inputs/plan-section-r3.md` in the pack), write that commit's full hash for `<RECORDS-PIN>` in
`dispatch.md`, and push the exchange commit named there. If it is replayed onto a newer exchange tip, its hash
changes: put the pushed hash in `dispatch.md` (and its parent) before dispatching.

**Ready to dispatch**
