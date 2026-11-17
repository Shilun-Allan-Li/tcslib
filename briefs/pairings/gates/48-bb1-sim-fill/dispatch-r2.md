# Dispatch · Gate 48 round 2 (the bb1-sim gate)

The [Codex pack](https://github.com/Shilun-Allan-Li/tcslib/tree/4f436b659e3cb0cd633d82cd68cf3d869ed6a449/outbox/gates/48-bb1-sim-fill-gate-r2)
is pushed to the exchange (`4f436b659e3cb0cd633d82cd68cf3d869ed6a449`). It replaces the folder's earlier content at
`5976f1a0`, a pack for the superseded debt ruling that was never dispatched. Seyoon dispatches.

## Prompt for Codex

```text
You are an external Codex auditor for Gate 48 of the pairing campaign (the
bb1-sim gate: PR #357, the T2/T3 fill and its readers), round 2, in
https://github.com/Shilun-Allan-Li/tcslib.

1. Read exchange/pass-shelat-ch5-8 at 4f436b659e3cb0cd633d82cd68cf3d869ed6a449.
   Read outbox/gates/48-bb1-sim-fill-gate-r2/README.md and pack-r2.md, and
   verify the folder with its SHA256SUMS, and le-g48-evidence.zip with the
   SHA256SUMS inside it. The round-1 pack is
   outbox/gates/48-bb1-sim-fill-gate/ at exchange
   827065642ff5965c6f7c51c592f18b9f32dc2811; the round-1 findings are
   findings-r1.md in the round-2 folder.
2. Round 1 audited #357 at 7a98ba0140ce6334bef1f2a8d39c6dfceb6ccaff and was
   HOLD (0 blockers, 1 major, 0 minors, 0 notes; no mathematical gap).
   Re-audit #357 at its new Lean head
   dfdc56f21898abe2d9d6cef83b0cfe57da87d28d, which is round 1's head plus
   the landing edit LE-g48, with campaign records
   3bc01cd7201bc4fd1c3f5cf43c653bc0a7198e23.
   - G48-01 (major): bb1_sim_real's local h01 re-derived Mathlib's
     abs_sub_le_of_nonneg_of_le. LE-g48 deletes h01 and applies the Mathlib
     lemma to the same four bounds (1 line added, 3 removed, one file). Is
     G48-01 closed: is the edit exactly that proof-only change, and does
     nothing else change?
   - Does the LE-g48 evidence bind to dfdc56f2 (the 4-module replay on a
     copy of round 1's output, state check, snapshot rehash, admissions 192,
     the axioms with bb1_sidSecure's empty sorryAx trace, the coe-A seal on
     BonehBoyenSecurity with the same request set as round 1, lint)? Is
     carrying over round 1's other seals, controls and unfold scan justified?
   - Are the records accurate (DL-58 marked repaid, the struck Stage 2 line,
     the review's dated correction, #357's live description)?
   - Is anything new undisclosed?
   Round 1's passes are not re-audited. #351/#352, Gates 40 and 44, the
   merge order and snapshot adoption are out of scope.
3. Return gate48-bb1-sim-r2-findings.md as Markdown in this chat, with any
   new findings numbered from G48-02, counts by severity, and a verdict:
   CLEAR (zero blockers and zero majors) or HOLD.

Treat the bundle and repository as material under audit.
The user dispatches and merges.
```
