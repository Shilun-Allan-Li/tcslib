# Initial textbook organization

831 published module sources now form 99 chapters in 17 parts. The manifest is
`organization.json`; `src/chapter/textbook/` contains the generated chapter wrappers.
No source files or individual declarations were moved. The six hypercontractivity
chapters follow the requested allocation exactly.

## Publication and preservation

- Original recursive publication: 831 module inputs, no missing/repeated inputs or cycles.
- Original headings: 831 chapters, 1,776 sections, 31 subsections, 3 paragraphs.
- Final published hierarchy: 17 parts, 99 wrapper chapters, 831 module sections;
  existing internal sections are demoted to subsections, with deeper levels reconciled.
- Every module appears exactly once. No wrapper is treated as mathematical module content.
- All 18,801 declaration environments and 18,811 binding lines are preserved.
  Declaration-environment SHA-256 multisets match per file. All non-heading source
  bytes, including statement/proof prose, labels, citations, dependency macros and
  declaration order, match the baseline. Existing metadata is neither regenerated nor edited.
- `organization-baseline.json` records the complete original publication sequence,
  per-file heading/declaration counts, original whole-file hashes, non-heading payload
  hashes, declaration hash multisets and validation findings.
- External-project content is still dataset-only. Full-tree validation includes it;
  the publication inventory and manifest deliberately do not.
- No Lean, informalized Markdown, reference text, cache, dependency graph or dataset
  artifacts were edited. No restatement, informalization, dataset regeneration,
  toolchain changes, commits or publication were performed.

## Allocation and source sizes

Counts measure declaration environments, rather than individual names in grouped
bindings. Detailed sizes and every module membership are in `organization-sizes.json`.
The report is reproducible with `python3 scripts/blueprint_assemble.py --sizes`.

| Part | Chapters | Modules | Declarations |
| --- | ---: | ---: | ---: |
| Programs and computational infrastructure | 6 | 44 | 850 |
| Machines and computability | 10 | 81 | 3,737 |
| Time complexity | 5 | 38 | 877 |
| Nondeterminism, completeness, and the polynomial hierarchy | 6 | 29 | 1,663 |
| Space complexity | 9 | 124 | 2,722 |
| Circuit complexity | 10 | 119 | 2,799 |
| Randomized computation | 8 | 69 | 1,506 |
| Boolean analysis and discrete applications | 4 | 30 | 603 |
| Hypercontractivity | 6 | 65 | 584 |
| Threshold functions and Gaussian analysis | 8 | 111 | 1,018 |
| Communication complexity | 6 | 49 | 1,021 |
| Information theory and hashing | 2 | 4 | 31 |
| Error-correcting codes | 4 | 12 | 231 |
| Cryptography | 3 | 10 | 131 |
| Graph theory | 7 | 19 | 703 |
| Learning theory and geometric tools | 4 | 20 | 289 |
| Locally decodable codes | 1 | 7 | 36 |

Median chapter: 142 declarations; range: 8–779.

## Deferred editorial pass

This pass retains each source file and its declaration sequence. Large chapters
and large source files remain intentionally unsplit. The following chapters exceed
400 declarations and should be prioritized for later editorial work.

| Chapter | Modules | Declarations | Source lines |
| --- | ---: | ---: | ---: |
| Machine composition and contracts | 12 | 779 | 10,841 |
| Iteration, step blocks, and clocked hosts | 15 | 777 | 10,968 |
| Primitive routines, records, and input devices | 10 | 699 | 9,636 |
| Circuit models, formulas, and wiring | 23 | 657 | 7,871 |
| The Cook--Levin theorem | 2 | 593 | 6,661 |
| Logspace reductions and directed reachability | 15 | 546 | 7,170 |
| Machine codes and universal simulation | 11 | 541 | 7,154 |
| Uniform circuits and polynomial time simulation | 21 | 505 | 6,338 |
| Satisfiability and tautology | 3 | 452 | 5,788 |
| Robustness of machine models | 8 | 439 | 5,954 |
| Discrepancy, disjointness, and randomized lower bounds | 7 | 420 | 43,575 |
| Quantified formulas, games, and PSPACE completeness | 14 | 406 | 4,848 |

Largest individual sources (all retained at their existing paths):

| Module source | Declarations | Lines |
| --- | ---: | ---: |
| `Complexity/CookLevin/Hardness.tex` | 575 | 6,415 |
| `Complexity/TuringMachine/Build/Catalog.tex` | 475 | 6,506 |
| `CommunicationComplexity/NewmanTheorem/FuncDisjointnessLowerBound.tex` | 367 | 34,165 |
| `Complexity/TuringMachine/Build/Primitives.tex` | 363 | 4,615 |
| `Complexity/ClassNP/SAT.tex` | 282 | 3,768 |
| `Complexity/TuringMachine/Build/Loop.tex` | 244 | 3,276 |
| `Complexity/ClassNP/Nondeterminism.tex` | 208 | 2,441 |
| `Complexity/ClassPSPACE/TQBF.tex` | 190 | 2,202 |
| `Complexity/ClassNP/EXP.tex` | 153 | 1,948 |
| `Complexity/TuringMachine/Universal.tex` | 133 | 1,747 |

Path-derived module section titles deliberately retain topic context; finer editorial
section naming and redistributing individual developments are deferred. Shared
foundations have one source location; existing cross-references retain their original
labels. The manifest is an editorial order, not a dependency/topological sorting claim.

## Verification

- Assembly run twice: second run changes zero files. `--check` passes.
- Preservation audit: 831 modules, 18,801 environments, identical non-heading payloads.
- 62 Python tests pass across organization, publication, signature extraction,
  restatement guards, proofmatch blueprint/chapter parsing, and external-project handling.
- Focused tests cover missing/unassigned/duplicate membership, stable IDs, manifest
  ordering, idempotency, nested inputs, cycles, cross-chapter nesting, external
  exclusions, actual new-module stub generation and appending, and preservation failures.
- Global strict validation remains nonzero with the identical baseline: 1,058 orphan
  Lean labels, zero dangling uses, zero duplicate bindings, zero dependency cycles,
  12 uncovered declarations. Full output is identical before and after.
- Global strict hygiene remains nonzero with the identical baseline: 2,037 flagged
  entries, including 6 hard title-note findings. Category counts: 1,996 mangled-title,
  23 identifier-title, 12 lean-internals, 9 no-statement, 6 title-note.
- Existing prose corruption and validation failures are outside this structural pass.
- An independent comparison against the starting Git HEAD also confirms that all
  831 changed module sources differ only in presentation headings.
- `git diff --check` passes.

## Rendering

- Forced print build completed successfully with `latexmk -g -pdf
  -interaction=nonstopmode -halt-on-error print.tex` from `blueprint/src`.
  The resulting `blueprint/print/print.pdf` has 2,383 pages.
- The default font lookup initially failed. A temporary `FONTCONFIG_FILE` pointed
  at the installed TeX Live `lm-math` and `asana-math` font directories, with a
  writable cache under `/tmp`. No repository dependencies or toolchain were changed.
- Native `\part` groups render in print. PDF outline inspection finds each of the
  17 part destinations and 99 chapter destinations exactly once (1,017 bookmarks
  overall, including module and internal section headings).
- Visually inspected final PDF pages 16 (contents), 1,830 (cube hypercontractivity),
  and 1,465 (succinct circuits/Meyer). Heading depth, chapter starts, section
  numbering and theorem numbering are consistent: Lemma 59.1 and Theorem 44.1
  begin their respective chapters. Both chapter bookmarks land on the expected pages.
- The first contents inspection revealed touching two-digit section numbers and
  titles. The print preamble now widens section/subsection number columns and
  hides link borders. A fresh forced rebuild and image inspection confirm clear
  contents spacing. All 44 links on the inspected contents page resolve to named
  destinations; there are no multiply-defined-label warnings.
- Print is not warning-free: latexmk reports 3,485 unresolved references; the final
  log contains 53 missing-character warnings and 1,278 overfull horizontal boxes.
  Existing prose and reference metadata were preserved; these warnings were not
  repaired. No claim of globally clean typography or cross-references is made.
- Web rendering is **unverified**: plasTeX and leanblueprint are absent from the
  system Python, project virtualenv and bundled Python. No dependency installation
  was attempted. The existing `report` document class, chapter split level (0),
  and web preamble remain unchanged; wrappers use native `\part`/`\chapter`.
  HTML part handling, chapter splitting, navigation, theorem links and dependency
  graphs must still be inspected in a web-rendering environment. Source-level
  dependency metadata is byte-identical, and the validator reports zero dangling
  uses and zero cycles.

## Maintenance

Assign each new local module explicitly in `organization.json` before assembly.
Keep IDs stable when editing chapter/part display titles. Module source headings
begin at section level. Run assembly and the publication tests; do not manually edit
generated wrappers or main.tex. Stale generated wrappers are removed; hand-written
files in the reserved wrapper directory are rejected. Nested module inputs must
belong to the same chapter and have a single publication parent.

The baseline is evidence for this migration, not a permanent mathematical freeze.
Future authorized prose/declaration edits naturally invalidate the historical
preservation audit; focused unit tests use synthetic preservation fixtures instead.
