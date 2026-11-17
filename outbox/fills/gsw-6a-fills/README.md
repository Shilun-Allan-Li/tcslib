# Claude fill `gsw-6a-fills` (GSW phase 6a units U4, U5, U7, U9, U10, U11)

Claude is the worker, a lead with up to 3 sub-agents on disjoint files (standing ruling: Claude for fills; the overnight
ruling of 2026-11-17 sends the 6a units the maintainer does not fill in-house to an external job that Seyoon
dispatches). The job is the fill phase of plan section r3 §H7 for six units, 41 `sorry`'d targets in six files:

| Unit | File | Rows | Targets |
|---|---|---|---|
| U4 | `Complexity/BranchingPrograms/BarringtonConverse.lean` | C17–C21 | 11 |
| U5 | `Complexity/BranchingPrograms/NC1.lean` | C22–C25 | 5 |
| U7 | `Complexity/CircuitComplexity/NANDLayering.lean` | N7–N13 | 7 |
| U9 | `Complexity/CircuitComplexity/FormulaArith/CarrySave.lean` | F5–F6 | 7 |
| U10 | `Complexity/CircuitComplexity/FormulaArith/Compare.lean` | F7–F8 | 7 |
| U11 | `Complexity/CircuitComplexity/FormulaArith/ModSum.lean` | F9–F10 | 4 |

**Not in this job (in-house):** U1 and U2 (proved as a draft on `fill/gsw-6a-u1-u2`), U3 (Barrington, in progress
there), U8 (`Combinators`) and U6 (`NANDForm`), in progress on `fill/gsw-6a-u8-u6`. Under the proved-modulo rule every
unit depends only on frozen statements, so units never share a file and all run in parallel.

**Base** (the bb1-sim fill's "synthetic merge now" precedent): `05999162b77c1f0fef64b07427e1a041a31b43d2`, tree
`7d551d6f5278fb79febe1b4eeffb4ca4329dc1d3`, a deterministic unsigned merge of #360's head
`3ea428fd8b99ffe33cdfb8dbe8068d0eb000d032` (the Q3 readers) into #359's head
`73aedcdaaaffef7e69ab012d9b9195f150bae68d` (the 6a statements, on #358 `a616adcac0760ab56b1b0a2a4869f4763843f9ab`).
- The merge is clean (`git merge-tree --write-tree`, rc 0). Its Lean equals the records pin
  `7cbd0c93cb053ab399aa40e9163a1229a1d99360` plus exactly the 21 Lean files of #358, #359 and #360.
- This commit object exists only where it is made: `tools/mkbase.sh` (or the `git merge --no-ff` recipe in the brief)
  re-creates it from the two pinned heads with fixed identity, dates and message, and checks tree and commit. The
  maintainer ran both forms and got `05999162…` both times.
- #358, #359 and #360 are **unmerged drafts**. Gate 45 (Codex, dispatched) audits #358/#359 and may still change a
  statement; any such change is handled by the maintainer, and the worker stays on the pinned base.

Read [the brief](brief.md) and the [environment addendum](fill-environment-addendum.md) (v1, Part 1 unchanged, with an
adaptation for this job that applies the user's 2026-11-17 Lean-parallelism ruling for cloud workers). Verify the
package with `shasum -a 256 -c SHA256SUMS` from this directory.

**Pack contents:**
- [Build order](order.txt): 218 TCSlib modules at the base, in import order: the upstream closure of every module
  downstream of a changed module, the root `TCSlib` excluded. It is a subsequence of the depth-first post-order of the
  1,440 modules reachable from `TCSlib.lean` and the two `audits/*/Checks` (imports in file order).
- [Closures](closures.txt): `CHANGED`, the 6 owned files; `DOWN`, 9 modules (the six, `FormulaArith`,
  `CircuitComplexity`, `BranchingPrograms`), the sweep; `INFO-DELTA`, the 21 modules whose source differs between the
  records pin and the base. Neither `audits/*/Checks` is downstream of a changed module.
- [Mathlib roots](roots.txt): 66, the Mathlib modules the 218 modules import directly.
- [Source hashes](SOURCE-SHA256SUMS) of the 218 files at the base, read from the git objects of tree `7d551d6f…`.
- [Base admissions](base-sorries.txt): **115 declarations in 18 modules** of the order, from a syntactic scan
  (comments and strings stripped, `sorry` tokens attributed to the enclosing declaration). They include the 41
  targets; the final must leave **74 in 12 modules**.
- [Targets](targets.txt): the 41 targets, with unit, row, `path:line` and full name.
- `tools/`: `mkbase.sh` (the base), and `graph.py`, `pins.py`, `targets.py` (how the pin files were made: `graph.py`
  and `pins.py` are the bb1-sim pack's, unchanged except a first docstring line).
- The exchange pack adds `inputs/` (with its own `SHA256SUMS`): plan section r3, `rulings.md`, the statement delivery's
  review (`final-6a-r1/review.md`, `phase2.md`), its checkpoint review, and the #360 review, byte-identical to the
  records at the pin (SHA-256 in the brief, *Inputs*).

**Maintainer's checks at staging** (no Lean run): both merge forms reproduce the base; the pin files were made by the
packaged tools from git objects; `style_lint` gives 0 findings in the six files and `campaign_style_lint
TCSlib/Complexity --check8b` gives 25 FAIL / 390 WARN over 513 files at the base (a sparse checkout of the base);
every TCSlib name the six files' sketches cite exists at the base; the sketches' "missing" readers are all supplied by
#360; `csaLevels k ≤ 2⌈log₂ k⌉` and its sketch's step re-checked numerically for `k < 200000`.

Claude returns at least one checkpoint and the final only at `inbox/fills/gsw-6a-fills/` on the exchange; each
checkpoint carries the head hash, the patches to it and `src/` of every file it claims compiles (lesson G6A-C1-F01). It
never pushes a campaign branch. Seyoon dispatches with the prompt in the records' `dispatch.md` (beside this file in
`briefs/lattice-gsw/phase6/issued-fills-r1/`; it is not part of the pack).

**Size** (maintainer's assessment). About 1,130–1,870 fill lines (r3 §H7; U7 up to about 300 by r3 §H8 item 19). The
long steps are mechanical: the 218-module bootstrap, the 9-module sweep, and four-variant seals of six owners at head
and base, all run through a memory-sized pool of Lean processes. One job is right. The suggested split gives the lead
U5, U11 and the integration; sub-agent `bp` U4; `layer` U7; `fa` U9 and U10.

**Maintainer steps before dispatch:** commit this folder to the records branch (the exchange pack equals it, plus
`inputs/`) and push the exchange commit named in `dispatch.md`. If it is replayed onto a newer exchange tip, its hash
changes: put the pushed hash in `dispatch.md` (and its parent) before dispatching.

**Ready to dispatch**
