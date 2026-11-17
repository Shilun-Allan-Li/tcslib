# Codex audit · Gate 49 round 1 · DW-11, the combined small-items gate: #351, #352 and #365

Audit three PRs together using pack-r1.md:
- #351, merged as cf7d28f7159b46033e8b8ae170954f9575e5d145 (head dfacac356ff1225aca4c900d81bbf2cabce7b499): the bb1-sim
  Games statements (Games/Relational.lean: expect_simulate_rel and expect_sample_rel as targets, prob_simulate_rel) and
  the public averaging bound ProbComp.abs_expect_sub_le_expect in Games/Probability.lean.
- #352, merged as 463f224414ab7615e54104be353bfcda9dfceda7 (head 92dea4f8126747ea7e816984349b9dbb789f0065): the group
  helpers pow_val_add, pow_val_neg and pow_val_bijective_of_ne_one in Pairing/Group.lean. It is the group-helper PR, not
  a reader follow-up.
- #365, open draft at 5eaddd171bceccee917929e7f319ff9202994c59 (base 5aed99076d2bd4e5d6f831aed88739fc3ce475b6): the
  follow-up fix ordered at this gate's pre-dispatch sweep. One generic lemma pow_val_bijective_of_prime_card, the two
  bijections re-proved from it, and Mathlib's pow_mod_card in three exponent laws. Proof-only apart from the new lemma.

#351 and #352 were merged on the maintainer review ("merge now, audit later"); a HOLD on either means a follow-up fix
PR, not a revert. Campaign records are pinned at ab17e37feb00a677d69f6abd5ff7e427e3b9ef3c, the commit that files the records copy of this pack.

The evidence is the maintainer's: phase 1 and phase 2 for #351 (181 modules rc 0 on snapshot #2; the merge's Lean equals
the replayed tree, adopted as snapshot #3), phase 2b for #352 (12 modules on snapshot #3; adopted as snapshot #4) and
#365's job report (22 modules rc 0 on the TS2 replay; coe-A seal of Group equal at base and head). No Lean was run for
this staging.

- pack-r1.md: scope, pins, rulings, the audit questions, the evidence binding, the known slips, the findings format.
- pr351.diff.txt, pr352.diff.txt, pr365.diff.txt: each PR's diff from its merge base (for #351 and #352 equal to the
  merge commit's first-parent diff).
- pr351-description.md, pr352-description.md, pr365-description.md: the PR bodies at staging.
- source-head-r1.json: pins, commits, signature kinds, and per-file hashes, line counts and widths.
- sources-r1.zip: the files at base and head for each PR, context at the records tip (relatives, the ETT averaging copy,
  helper consumers), the two Mathlib files holding the nearest relatives, and the BGZ09, Sho04 and BB04 transcriptions.
- verification-r1.zip: the four evidence ZIPs (nested unchanged), the snapshot #3 and #4 adoption records, the staging's
  git-object checks and duplication sweep with their scripts, the records (reviews, report, rulings, design note,
  issued statement brief, policy, Gate 44/47/48 findings, extracts) and the PR REST fields. MANIFEST.md gives
  provenance; its SHA256SUMS lists every other entry.
- bundle.md: the pack, the reviews and report, the rulings, the PR descriptions, the record extracts, the checks, the
  diffs, the Lean files at the heads, the design note, Gate 44's and Gate 48's round-1 findings, the BGZ09 and Sho04
  transcriptions and policy.md. Each section header names its path and source; BUNDLE-FILES.txt lists them.

Check SHA256SUMS before using the pack. Return gate49-dw11-findings.md as Markdown in the chat, with findings numbered
G49-NN and a verdict per PR and overall of CLEAR or HOLD. If you have several evidence files, return a ZIP containing
that Markdown and the evidence. The user dispatches and merges.
