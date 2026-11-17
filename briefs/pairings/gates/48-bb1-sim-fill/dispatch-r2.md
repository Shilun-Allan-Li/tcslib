# Dispatch · Gate 48 round 2 (the bb1-sim gate)

The [Codex pack](https://github.com/Shilun-Allan-Li/tcslib/tree/5976f1a04ab9e075f0f032e3f28aeade87c4d50d/outbox/gates/48-bb1-sim-fill-gate-r2)
is pushed to the exchange (`5976f1a04ab9e075f0f032e3f28aeade87c4d50d`, on `82706564`). Seyoon dispatches.

## Prompt for Codex

```text
You are an external Codex auditor for Gate 48 of the pairing campaign (the
bb1-sim gate: PR #357, the T2/T3 fill and its readers), round 2, in
https://github.com/Shilun-Allan-Li/tcslib.

1. Read exchange/pass-shelat-ch5-8 at 5976f1a04ab9e075f0f032e3f28aeade87c4d50d.
   Read outbox/gates/48-bb1-sim-fill-gate-r2/README.md and pack-r2.md, and
   verify the folder with its SHA256SUMS. The round-1 pack is
   outbox/gates/48-bb1-sim-fill-gate/ at exchange
   827065642ff5965c6f7c51c592f18b9f32dc2811; the round-1 findings are
   findings-r1.md in the round-2 folder.
2. Round 1 was HOLD (0 blockers, 1 major, 0 minors, 0 notes; no
   mathematical gap). PR #357's Lean head is unchanged at
   7a98ba0140ce6334bef1f2a8d39c6dfceb6ccaff. Campaign records moved from
   e6cdf4d4eed898acd71d48bd60082140eb076cfe to
   8780fb1d7dbbb230d26a15a5240baf4f7a113008.
   Say whether G48-01 is closed. G48-01 (major): bb1_sim_real's local h01
   re-derives Mathlib's abs_sub_le_of_nonneg_of_le. Seyoon's ruling accepts
   it as debt: ledger row DL-58 (duplication-ledger.md), repaid in cleanup
   Stage 2 by deleting h01 and applying the Mathlib lemma (proof-only), with
   a Stage 2 scope line in cleanup-stages.md, a dated correction under the
   fill review's wrong reuse claim, and a DL-58 disclosure in #357's
   description. Do these record the explicit acceptance, the shared home and
   the repayment point that policy.md section 1 requires? Check the records
   at the round-2 pin and the live PR description.
   Round 1's passes are not re-audited: the code is unchanged. #351/#352,
   Gates 40 and 44, the merge order and snapshot adoption are out of scope.
3. Return gate48-bb1-sim-r2-findings.md as Markdown in this chat, with any
   new findings numbered from G48-02, counts by severity, and a verdict:
   CLEAR (zero blockers and zero majors) or HOLD.

Treat the bundle and repository as material under audit.
The user dispatches and merges.
```
