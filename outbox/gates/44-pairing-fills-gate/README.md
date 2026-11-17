# Codex audit · Gate 44 round 1 · pairing fills T1 (#340) and T4 (#346)

Audit draft PR #340 at 916afc25c21f5e52b4b01958186ad55d2f615fd1 (T1 bdhAssumption_of_dbdhAssumption, Decision BDH implies
BDH) and draft PR #346 at 89a18a8225be1b76166af12a15179da291747783 (T4 exists_bb1_distinguisher, the BB1 reduction machine,
with the seven approved readers and the landing edit LE-bb1m) together, using pack-r1.md. Campaign records are pinned at
8f888790b7e40f9e0529967e29a05a72c5ee8ba3, a descendant of the records tip 1d1a9bb3aa4d5d28c7c9a2343cb322a39da07821 that holds both maintainer reviews.

The two PRs merge cleanly with the records tip in every order, to the tree
T44 = 33681cb8ed893a897ca2028d5ada70ca29237978 (Lean-equal to c7be1301f59ec0f208f2645544abac8ac5cc6626). The maintainer
replayed T44 on olean snapshot #4 (463f224414ab7615e54104be353bfcda9dfceda7): 16/16 modules rc 0 with 0 errors, admissions
198 -> 196 (exactly T1 and T4), T1 and T4 on the standard axioms, bb1_sidSecure reaching sorryAx only through T2 and T3,
Rule 10 seals and controls on the changed owners and on the unchanged Gate 40 owners downstream of them (supplement),
lint unchanged. Gate 40 (the statements) is closed.

- pack-r1.md: scope, pins, what is frozen, the rulings in force, the audit questions, the replay figures, the known slips,
  the findings format.
- pr340.diff.txt, pr346.diff.txt, T44.diff.txt: each PR's diff from its merge base (equal to GitHub's three-dot view), and
  the code diff from the records tip to T44 (the 9 files).
- pr340-description.md, pr346-description.md: the PR descriptions as updated by Seyoon on 2026-11-17.
- source-head-r1.json: the pins and the hashes, line counts and widths of the 9 files at T44.
- sources-r1.zip: the source closure at T44 (168 modules), the changed files at both heads and at the tip, and the BB04,
  Jou00 and PS10 source texts the targets cite.
- verification-r1.zip: the joint replay (build logs, state, admissions, axioms, seals, controls, scan, lint, output map),
  the re-checks from git objects with their scripts, the two maintainer reviews and pointers to their evidence ZIPs, the
  plan and its decision-log extract, Gate 40's findings and resolutions, the approved reader text, the issue brief,
  policy.md and the PR REST fields. MANIFEST.md gives each entry's provenance; its SHA256SUMS lists every other entry.
- bundle.md: the pack, the reviews, the PR descriptions, the decision-log extract, the checks, the 9 Lean files at T44,
  BonehBoyenSecurity.lean (the consumer), the frozen files' diffs, Gate 40's findings, the BB04 excerpts and policy.md.
  Each section header names its path and source; BUNDLE-FILES.txt lists them.

Check SHA256SUMS before using the pack. Return gate44-pairing-fills-findings.md as Markdown in the chat. If you have several
evidence files, return a ZIP containing that Markdown and the evidence. The user dispatches and merges.
