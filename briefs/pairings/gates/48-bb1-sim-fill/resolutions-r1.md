# Gate 48 · resolutions, round 1 · HOLD → ruling and ledger row (no code change)

Codex's verdict is **HOLD**: 0 blockers, 1 major, 0 minors, 0 notes.
- **Findings:** `findings-r1.md` (verbatim, filed by the maintainer; the evidence ZIP it mentions was not received).
- **Audited:** #357 at `7a98ba0140ce6334bef1f2a8d39c6dfceb6ccaff`; records `e6cdf4d4`; exchange `82706564`.

Codex found **no mathematical gap**. Its confirmations:
- **Proofs.** The four targets establish their frozen statements, edge cases included; no helper is false, vacuous or
  an assumption in disguise.
- **Integrity.** Frozen check 12/12 with 8 controls; decls2 69/0/0; the ten readers are verbatim at their anchors;
  LE-bsf1 is comment-only apart from the `rfl` reader `bb1RealState_eq`.
- **Rule 10.** 36 head and 16 base seals recounted; 36/36 phase-2 seal sources and 64/64 control sources reconstructed;
  485 sealed negatives per harness, each failing once; 0 foreign unfolds.
- **Replay and axioms.** 19/19 bind to the head; admissions 196 → 192; all six traces empty, including
  `bb1_sidSecure`'s.
- **Other duplication.** None beyond G48-01 across 529 cryptography files and #355's `Games/Tapes.lean`.
- **Grades.** BSF-F01–F08 agreed, except BSF-F04 regraded major before acceptance and closed at the pin by Q1/DL-57.

| Finding | Grade | Resolution | Evidence and pointer |
|---|---|---|---|
| G48-01 | **major** | **Accepted and ledgered** (Seyoon, 2026-11-17, ruling G48-01, choosing debt over a landing edit). `bb1_sim_real`'s local `h01` (`BonehBoyenSecurity.lean:128–134`) re-derives Mathlib's `abs_sub_le_of_nonneg_of_le` (`Mathlib/Algebra/Order/Group/Abs.lean:119–124` at the pinned `029db123`, additive form of the `@[to_additive]` lemma; already used in `LWE/BitNoise.lean:110`). It is retained, and the debt is repaid in cleanup Stage 2 as ledger row **DL-58**: delete `h01` and close the bad-coin branch with the Mathlib lemma applied to the four `ProbComp.prob_nonneg`/`prob_le_one` bounds (proof-only). The phase-1 review's reuse claim keeps its text, with a dated correction beneath it. The round-1 pack (`pack-r1.md:254–255`) stays as filed. The PR #357 description now discloses DL-58. **No code change**: the head stays `7a98ba01`, so every round-1 pass and all evidence carry over unchanged. | `briefs/pass-shelat-ch5-8/duplication-ledger.md` row DL-58; `cleanup-stages.md` § Stage 2 (the G48-01 line); `fills/bb1-sim/fill-final-r1/review.md` (correction under § Duplication and reuse); the plan's ruling row of 2026-11-17. |

Then Gate 48 round 2 (Codex) at the same head `7a98ba01`, checking only the G48-01 resolution against policy §1
(explicit acceptance, shared home, repayment point), as Gate 44 round 2 did for G44-01.
