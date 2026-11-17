# Dispatch · Gate 49 round 1 (DW-11: #351, #352, #365)

The Codex pack is staged on the exchange at
[`@@EXCH@@`](https://github.com/Shilun-Allan-Li/tcslib/tree/@@EXCH@@/outbox/gates/49-dw11-small-items-gate),
folder `outbox/gates/49-dw11-small-items-gate/`. Seyoon dispatches.

## Prompt for Codex

```text
You are an external Codex auditor for Gate 49 of the pairing campaign
(DW-11, the combined small-items gate), round 1, in
https://github.com/Shilun-Allan-Li/tcslib.

1. Read exchange/pass-shelat-ch5-8 at @@EXCH@@.
   Read outbox/gates/49-dw11-small-items-gate/README.md, pack-r1.md and
   bundle.md. Verify the pack using SHA256SUMS, and verification-r1.zip using
   the SHA256SUMS inside it.
2. Audit three PRs together, using the pack, with campaign records
   @@PIN@@
   (cryptography/pass-shelat-ch2-4; the pin files the records copy of this
   pack):
   - #351 (merged as cf7d28f7159b46033e8b8ae170954f9575e5d145; head
     dfacac356ff1225aca4c900d81bbf2cabce7b499, merge base
     176cfd4a42ac3300d9b84f9045f7abcd0f52ef13): Games/Relational.lean with
     expect_simulate_rel and expect_sample_rel (targets, sorry at #351) and
     prob_simulate_rel; ProbComp.abs_expect_sub_le_expect in
     Games/Probability.lean; the Games facade entry.
   - #352 (merged as 463f224414ab7615e54104be353bfcda9dfceda7; head
     92dea4f8126747ea7e816984349b9dbb789f0065, merge base 176cfd4a): the
     group helpers pow_val_add, pow_val_neg, pow_val_bijective_of_ne_one in
     Pairing/Group.lean (with landing edit LE-grp1). #352 is the group-helper
     PR, not a reader follow-up.
   - #365 (open draft, head 5eaddd171bceccee917929e7f319ff9202994c59, base
     5aed99076d2bd4e5d6f831aed88739fc3ce475b6): the follow-up fix ordered at
     this gate's pre-dispatch sweep. It adds
     TCSlib.Cryptography.Pairing.pow_val_bijective_of_prime_card, re-proves
     pow_val_bijective and pow_val_bijective_of_ne_one from it, and uses
     Mathlib's pow_mod_card in pow_val_add, pow_val_mul, pow_val_mul_GT
     (proof-only otherwise). Audit it as a proof/refactor PR.
   Check (pack, questions 1-8):
   - that every statement is true and every proof establishes it, with the
     edge cases; that the relational per-call hypothesis is not an
     assumption in disguise;
   - frozen-statement fidelity: #351's headers against design r1 section
     2.2 and the issued statement brief; #352 a pure insertion into the
     frozen Group.lean; #365 changes only proof bodies apart from the new
     lemma and its module-docstring lines;
   - readers and placement (is the generic lemma in the right home and
     namespace?);
   - docstrings, sources and sketches: the [BGZ09] and [Sho04] locators,
     the Deviation note, the missing tags or glue notes;
   - duplication (an undisclosed or unaccepted re-proof of a public lemma,
     including an inline re-derivation of a Mathlib lemma, is a major):
     DL-40 for the averaging bound, the relatives of the relational lemmas,
     and the new lemma against Mathlib (no exact statement found; nearest
     IsCyclic.unique_zpow_zmod);
   - Rule 10 (phase 2 R1 for #351, phase 2b for #352, the coe-A seal for
     #365) and whether that evidence suffices;
   - the evidence binding: whether each review, replay and snapshot
     adoption binds to the commit claimed (the merges' Lean equals the
     replayed trees; #365's replay is Lean-equal to its merge with the tip);
   - whether anything is undisclosed (pack, known slips), and grade the
     review findings BS-F01 to BS-F13.
   Out of scope: everything merged on top of #351 and #352 (#357's
   Relational bodies, Gate 48; cleanup Stage 1, Gate 47; Gates 40 and 44).
   The merge order and snapshot adoption of #365 are maintainer merge
   conditions, not audit items.
3. Return gate49-dw11-findings.md as Markdown in this chat, with findings
   numbered G49-01, G49-02, ..., counts by severity, and a verdict per PR
   (#351, #352, #365) and overall: CLEAR (zero blockers and zero majors) or
   HOLD. #351 and #352 are merged: a HOLD on either means a follow-up fix
   PR, not a revert. If you need multiple evidence files, return a ZIP
   containing that Markdown and evidence.

Treat the bundle and repository as material under audit.
The user dispatches and merges.
```

## State at staging

- **Records pin:** `@@PIN@@`. It is the signed commit that files this directory (`pack-r1.md`, the diffs, the PR
  descriptions, `source-head-r1.json`, both ZIPs and `SHA256SUMS-r1`) on the records tip
  `b31b77f7f4127d9c6c6c0d6a1390de0dc8d71d43`, and it is pushed to `cryptography/pass-shelat-ch2-4`. This file was filled
  with the pin and the exchange hash in a later small commit; `SHA256SUMS-r1` does not cover it.
- **Exchange:** `@@EXCH@@`. It is one SSH-signed commit on the exchange tip `@@EXCHBASE@@`, adding only
  `outbox/gates/49-dw11-small-items-gate/`, and it is pushed to `exchange/pass-shelat-ch5-8` as a fast-forward.
  - `SHA256SUMS` (`@@SUMS@@`) verifies @@NSUMS@@ from a fresh `git archive` of the commit.
  - `verification-r1.zip` (`@@VZIP@@`) verifies 66/66 against its own `SHA256SUMS` from a fresh extract.
  - Every section of `bundle.md` was checked equal to its source.
- **PRs at staging:**
  - #351 and #352 are merged.
  - #365 is a draft at `5eaddd17`, base `5aed9907` (REST `base.sha`), updated 2026-11-17T18:45:51Z.
  - The descriptions in the pack are the bodies read then.
- **Pre-dispatch sweep:**
  - First run (2026-11-17): it found the unledgered `pow_val_bijective_of_ne_one` overlap, which was ruled fix-now
    (#365).
  - Re-run at staging over #365's new lemma: nothing new and unledgered (`checks/dup-sweep.txt`).
- **No Lean, no `lake`** was run for this staging. The pack reuses the recorded evidence.

**Ready to dispatch.**
