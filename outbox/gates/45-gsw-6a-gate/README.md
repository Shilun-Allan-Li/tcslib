# Codex audit · Gate 45 round 1 · the GSW 6a gate: O1 (#358) and the 6a statements (#359)

Audit two stacked draft PRs using pack-r1.md. PR #358 (O1) at a616adcac0760ab56b1b0a2a4869f4763843f9ab moves the
balanced-tree combinators from TreeNCAC.lean into Complexity/CircuitComplexity/FormulaArith/Combinators.lean as the public
TreeCircuit.balanced, with five Rule 10 repairs and every TreeNCAC statement unchanged; it is audited as a proof/refactor.
Its merge base is the records tip e1d39836ed4a69a34914c35f4c73c71de853dcc6, whose Lean equals the #346 merge
3f540c22360c869069a0fba684e23ce6f3cb20db (olean snapshot #5). PR #359 at 73aedcdaaaffef7e69ab012d9b9195f150bae68d, stacked on
#358, adds the 6a statements under Complexity/: branching programs, Barrington's theorem in both directions (BWBP = NC1),
the NAND form and its layering, and the formula-arithmetic layer, with 98 targets admitted and the landing edit LE-ren
(TreeCircuit.rename dropped for the public reidx family). It gets a fidelity audit of all 98 targets against Bar89, BV14,
BV11 and plan section r3. Campaign records are pinned at 8c5875fa268a622e4e166da5f7a992715097c2c7, the base plus five
records-only commits.

The maintainer replayed both heads on snapshot #5: R1 9/9 and R2 20/20 modules rc 0 with 0 errors, state 1429 and 1440 OK,
admissions +0 and +98 (exactly the 98 targets), axiom logs byte-identical to the snapshot-#4 run (sorryAx in exactly the
98 targets and 5 dependents of N2, N12, N13), canonical coe-A seals re-run with every owner record equal to the #4 run,
root coe-A 14,074 requests with 0 errors. The strict and coe-B seals, the paired controls and the unfold scan are carried
forward from #4 on equal closure keys; the pack asks you to confirm or refute that argument. Out of scope: the Q3
owner-side reader PR, any in-house 6a fills, 6b (Gate 46), bootstrapping and circular security, and [Gen09].

- pack-r1.md: scope, pins, what changed, the rulings in force, the audit questions, the replay figures, the known slips,
  the merge interaction, the findings format.
- pr358.diff.txt, pr359.diff.txt: each PR's diff from its base (equal to GitHub's three-dot view; 4 files +279/-184 and
  17 files +3383/-2).
- pr358-description.md, pr359-description.md: the PR descriptions at staging.
- source-head-r1.json: the pins, both PRs' commits, and the hashes, line counts and widths of every changed file.
- sources-r1.zip: the 17 Lean series files at the #359 head, #358's 4 files at its head, the series files at the base,
  the unchanged modules the new files import or cite, and the Bar89, BV14 and BV11 ingests.
- verification-r1.zip: the staging's git-object checks (series, blobs, LE-ren, targets, sorryAx dependents, tags, sizes,
  merge trees, tools) with their scripts; the phase-1 review evidence (whole); the phase-2 and snapshot-#5 re-replay
  evidence summaries with their full manifests; the delivery's small files and its 30 paired controls; the records
  (plan r3, rulings, reviews, issued package, Gate 44 findings, policy.md, workflow.md, decision-log rows, ledger row
  DL-54); and the PR REST fields. MANIFEST.md gives each entry's provenance, POINTERS.md what is not copied; its
  SHA256SUMS lists every other entry.
- bundle.md: the pack, the reviews, the rulings, the worker's REPORT (read at the exchange delivery commit d7a9adb5), the
  PR descriptions, the extracts, the checks and key evidence summaries, both PR diffs, the 12 Lean files with targets or
  moved proofs at the #359 head and TreeNCAC at the base, plan section r3, the issued brief, the Bar89, BV14 and BV11
  ingests, Gate 44's findings, policy.md and workflow.md. Each section header names its path and source;
  BUNDLE-FILES.txt lists them.

Check SHA256SUMS before using the pack. Return gate45-gsw-6a-findings.md as Markdown in the chat, with findings numbered
G45-NN and a verdict of CLEAR or HOLD. If you have several evidence files, return a ZIP containing that Markdown and the
evidence. The user dispatches and merges.
