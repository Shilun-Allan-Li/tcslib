# Codex audit · Gate 47 round 1 · the cleanup Stage 1 gate: DW-5 (#347) and the Stage 1 promotions (#355)

Audit two stacked draft PRs together using pack-r1.md. PR #347 at daa6e173cdd94cad1475b9a96eca613bce53ba61 (DW-5; base
cryptography/pass-shelat-ch2-4, merge base 2da7e0f3cd65ec93ed71813b7828c3b66ba18942) adds nine typed-view readers to the
derand host files and re-derives E1 computesFunInTime_find and polyTimeComputable_find through them, clearing derand F-01's
20 IterateFind seal failures with every statement unchanged; it is audited as a proof/refactor. PR #355 at
d3c7cb00092ad5913904654d922f30fc7d5fce4a (cleanup Stage 1; stacked on #347) adds 69 declarations by pure insertion
(decls2 69/0/0; 21 files +1,079/-0): the general forms of the duplication ledger's copies in their shared homes, per the
CS1 rulings. It is audited as new public API: true, general, correctly homed, additive, documented, and free of
undisclosed duplication. Campaign records are pinned at 659542ecd9413b504d30da8c937b9805e6c1f71f, which already holds the
#357 merge, olean snapshot #6 and Seyoon's rulings on the pack's duplication sweep (ledger rows DL-59, DL-60).

The maintainer replayed TS1 = 1eaf940b938bb52e3919f5569893b58522df599b (the records tip e1d39836 x #347 x #355) on olean
snapshot #5: 556/556 modules rc 0 with 0 errors, state 1429/1429 OK, admissions 196 = 196 module by module, axioms
standard (census 1224 constants, no sorryAx), seals A/B strict/coe on 21 owners with no failure in a touched declaration
in the coe variants (strict-only failures are the FinDist coercion, B-only ones PolyExpr.eval, both notation by ruling;
every other failure pre-existing and identical at the tip), IterateFind 20 -> 0 in all four variants, controls ALL_OK,
0 foreign unfolds in touched declarations, lint 92/104 -> 92/103. The pack carries phase 2's seven disclosures and the
maintainer's own duplication sweep over all 78 new declarations: the overlaps the ledger already covered, and seven
more (B1-B7) that the sweep found and Seyoon ruled before dispatch (B1 accepted as DL-59, unified in Stage 2; B2-B7 as
DL-60). The pack asks whether those rows satisfy policy.md's duplication rule. Out of scope: Stage 2's changes (including the 14 approved blocks-alias changes), DW-10's inventory,
#351/#352 (DW-11) and the Complexity handoff.

- pack-r1.md: scope, pins, what changed, the rulings in force, the audit questions (A-E), the replays, the mandatory
  disclosures, the duplication sweep, the known slips, the merge interaction, the findings format.
- pr347.diff.txt, pr355.diff.txt: each PR's diff from its base (equal to GitHub's three-dot view; 3 files +253/-296 and
  21 files +1079/-0).
- pr347-description.md, pr355-description.md: the PR descriptions at staging.
- source-head-r1.json: the pins, both PRs' commits, and the blobs, hashes, line counts and widths of the 23 TS1 paths.
- sources-r1.zip: the 23 Lean files at TS1, the 21 existing ones at the base, #347's 3 files at its head, and the 25
  files the duplication sweep cites.
- verification-r1.zip: the staging's git-object checks (series, insertion, sizes, merge trees, import overlap,
  duplication sweep) with their scripts; summary subsets of the phase-1, phase-2 and DW-5 evidence with the original
  SHA256SUMS lines; the worker's report layer; the records at the pin; the PR REST fields. MANIFEST.md gives each
  entry's provenance, POINTERS.md the whole evidence zips by path and SHA-256; its SHA256SUMS lists every other entry.
- bundle.md: the pack, the reviews, the stage records, the ledger, the DW-5 record, the worker's report layer, the PR
  descriptions, the checks and key evidence summaries, both PR diffs, the #347 files and the two new modules at TS1,
  LazySampling.lean, policy.md, workflow.md and the Gate 44/45/48 findings. Each section header names its path and
  source; BUNDLE-FILES.txt lists them.

Check SHA256SUMS before using the pack. Return gate47-cleanup-stage1-findings.md as Markdown in the chat, with findings
numbered G47-NN and a verdict per PR and overall of CLEAR or HOLD. If you have several evidence files, return a ZIP
containing that Markdown and the evidence. The user dispatches and merges.
