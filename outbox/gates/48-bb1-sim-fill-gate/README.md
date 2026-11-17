# Codex audit · Gate 48 round 1 · the bb1-sim gate: T2/T3 fill and the ten readers (#357)

Audit draft PR #357 at 7a98ba0140ce6334bef1f2a8d39c6dfceb6ccaff (the bb1-sim fill: T2 bb1_sim_real, T3 bb1_sim_random,
the Games/Relational targets expect_simulate_rel and expect_sample_rel, the ten approved reader insertions in
IdentityBased/Defs.lean and BonehBoyen.lean, five helper modules under IdentityBased/BonehBoyenSecurity/, and the landing
edit LE-bsf1), using pack-r1.md. Its base is the records tip e1d39836ed4a69a34914c35f4c73c71de853dcc6, whose Lean equals
the #346 merge 3f540c22360c869069a0fba684e23ce6f3cb20db (olean snapshot #5). Campaign records are pinned at
e6cdf4d4eed898acd71d48bd60082140eb076cfe, the base plus one records-only commit.

The maintainer replayed the head on snapshot #5: 19/19 modules rc 0 with 0 errors and 0 sorry, state 1432/1432 OK,
admissions 196 -> 192 (exactly the four targets), 76 constants on the standard axioms, bb1_sidSecure with an empty
sorryAx trace, 36 Rule 10 seals with 0 errors, paired controls ALL_OK in strict and coe (485 sealed negatives per
harness, each failing once), 0 foreign unfolds, lint unchanged. #351 and #352 (merged) are out of scope (DW-11); Gate 44
(T1, T4) and Gate 40 (the statements) are closed.

- pack-r1.md: scope, pins, what is frozen, the rulings in force, the audit questions, the replay figures, the known slips,
  the merge interaction, the findings format.
- pr357.diff.txt: the PR's diff from its base (equal to GitHub's three-dot view; 9 files, +1925/-21).
- pr357-description.md: the PR description at staging.
- source-head-r1.json: the pins, the five commits, and the hashes, line counts and widths of the 9 files.
- sources-r1.zip: the 9 files at the head, the 4 existing ones at the base, the unchanged modules they import directly
  (and T4's Oracles.lean), and the BB04, BGZ09 and Sho04 transcriptions.
- verification-r1.zip: the phase-1 review evidence (whole) and the phase-2 evidence (all but 7 large raw files) of the
  maintainer review, the staging's git-object checks (series, pins, merge trees, tags, DL-57) with their scripts, the
  records (design note, rulings, reviews, issued brief and reader blocks, Gate 44 findings, policy.md, decision-log,
  ledger and cleanup extracts) and the PR REST fields. MANIFEST.md gives each entry's provenance, POINTERS.md what is not
  copied; its SHA256SUMS lists every other entry.
- bundle.md: the pack, the reviews, the rulings, the worker's REPORT (read at the exchange delivery commit 2467bc3b), the
  PR description, the extracts, the checks and key evidence summaries, the PR diff, the 9 Lean files at the head, the
  approved reader blocks, the design note, Gate 44's findings, the BB04 transcription and policy.md. Each section header
  names its path and source; BUNDLE-FILES.txt lists them.

Check SHA256SUMS before using the pack. Return gate48-bb1-sim-findings.md as Markdown in the chat, with findings numbered
G48-NN and a verdict of CLEAR or HOLD. If you have several evidence files, return a ZIP containing that Markdown and the
evidence. The user dispatches and merges.
