# Codex audit · Gate 50 round 1 · the GSW 6a fills gate: #366 (with LE-g50) and #368

Audit two open draft PRs together using pack-r1.md:
- #366 at 597fb736e545706a058cc212243a13f6dadfeceb (tree df05652d512a702fa8e379fe3f16258f0e1d20d5, merge base
  555f0fe1b10a20d1be72386a97c6fe7a2f39c204): the proofs of all 98 GSW 6a targets that Gate 45 froze at #359
  (d154c8830fc8ffc52671b41992e7dbef61e30959). In scope: #360's 15 owner readers, #360 addendum 2 (four promoted
  helpers), the in-house fills U1/U2, U3, U8 and U6, the external worker's U4, U5, U7, U9, U10 and U11, the landing edits
  LE-gf1 to LE-gf4 (LE-gf2 is a ruled freeze exception to the layerNAND docstring), the two merges of the records tip, and
  LE-g50, the fix of this gate's pre-dispatch duplication sweep (U1-U3). #366 contains #358 and #359, audited at Gate 45
  and out of scope.
- #368 at 1953898b18a33ab2cd533820c5754a1aacffeb44 (base 55f553715f280be36827ad86a94c93db39ec56c3): the public
  decrypt_eq_decode_dotProduct in GSW/Scheme.lean, promoted from step 1 of the private decrypt_eq_decode_errorSum, and
  the hybridPlant_eq reader.

Campaign records are pinned at b1392d065d0a8f496db8e01b6bdad746bc847ffe, the commit that files the records copy of this
pack; its parent is the records tip f19b8056, whose Lean is olean snapshot #8's.

The evidence is the maintainer's: phase 1 (static) on the worker's delivery; phase 2 on snapshot #6 (564 modules rc 0,
admissions 0 in the 6a modules, standard axioms for all 98 targets, coe-A on 22 owners, root coe-A, paired controls,
unfold scan); the re-replay at 93ae671e on snapshot #7 + #365 (byte-equal outputs where keys are unchanged); LE-g50 at
597fb736 on #8 (16 modules rc 0; TreeNCAC's pre-existing seal failures cleared); and #368's replays on #7 and, at its
merge with the tip, on #8. No Lean was run for this staging.

- pack-r1.md: scope, pins, what changed, the rulings in force, the audit questions, the evidence binding, the known
  slips, the merge interaction, the findings format.
- pr366.diff.txt: #366's PR view (merge base to head; includes #358/#359). pr366-360.diff.txt, pr366-fills.diff.txt,
  pr366-leg50.diff.txt: the in-scope segments. pr368.diff.txt: #368's diff.
- pr366-description.md, pr368-description.md: the PR bodies at staging.
- source-head-r1.json: pins, segments, every first-parent commit, and per-file hashes, line counts and widths.
- sources-r1.zip: the Lean files at the head, at the Gate-45 freeze, at the merge base and before LE-g50; #368's files;
  the pinned Mathlib and Batteries files with the reused lemmas and nearest relatives; the Bar89, BV14, BV11 and GSW13
  transcriptions.
- verification-r1.zip: the seven evidence ZIPs and the landing-edit diff (nested unchanged), the snapshot #7 and #8
  adoption records, the staging's git-object checks (series, Lean equality, merge trees, the frozen check with controls,
  the duplication sweep) with their scripts, the records (reviews, phase 2, the in-house REPORT, the #360 review and
  addendum, the 6b checkpoint review, rulings, plan section r3, the issued fills brief, Gate 45 findings, policy, extracts)
  and the PR REST fields. MANIFEST.md gives provenance; its SHA256SUMS lists every other entry.
- bundle.md: the pack, the reviews and records, the PR descriptions, the extracts, the checks, the in-scope diffs, the 18
  changed 6a and #360 Lean files at the head, #368's two files, Gate 45's findings, the issued brief, the Bar89 and GSW13
  transcriptions and policy.md. Each section header names its path and source; BUNDLE-FILES.txt lists them.

Check SHA256SUMS before using the pack. Return gate50-gsw-6a-fills-findings.md as Markdown in the chat, with findings
numbered G50-NN and a verdict per PR and overall of CLEAR or HOLD. If you have several evidence files, return a ZIP
containing that Markdown and the evidence. The user dispatches and merges.
