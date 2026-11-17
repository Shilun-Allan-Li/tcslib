# Gate 48 · resolutions, round 1 · HOLD → landing edit LE-g48

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
| G48-01 | **major** | **Fixed by landing edit LE-g48** on #357: commit `dfdc56f21898abe2d9d6cef83b0cfe57da87d28d` on `7a98ba01`, signed by the records key. In `bb1_sim_real` (`BonehBoyenSecurity.lean`), the local `h01` is deleted and the bad-coin branch reads `exact abs_sub_le_of_nonneg_of_le (ProbComp.prob_nonneg _ _) (ProbComp.prob_le_one _ _) (ProbComp.prob_nonneg _ _) (ProbComp.prob_le_one _ _)`, as Codex proposed. Proof-only: 1 line added, 3 removed, nothing else changes. *History:* Seyoon first ruled to accept the overlap as debt (DL-58, Stage 2), then asked for the fix before round 2, which had been staged at exchange `5976f1a0` but not dispatched. DL-58 stays in the ledger marked **repaid by LE-g48**; the Stage 2 line is struck. The phase-1 review's wrong reuse claim keeps its text with a dated correction and an update beneath it. #357's description now records LE-g48. | `le-g48.md`, `le-g48.diff.txt`, `le-g48-evidence.zip` (`ec54e109…`). Ledger DL-58; `cleanup-stages.md` (struck line); `fills/bb1-sim/fill-final-r1/review.md` (correction and update). |

**Checks at the new head `dfdc56f2`** (detail in `le-g48.md`):
- The diff from `7a98ba01` is exactly the 3-line change; `h01` occurred nowhere else (not in the docstring or sketch).
- **Replay** on a `cp -al` copy of #357's phase-2 output (`olean-replay-bb1sim` → `olean-replay-bb1sim-g48`): the plan
  rebuilds 4 modules (`BonehBoyenSecurity`, `IdentityBased`, `AdvancedEncryption`, `TCSlib`) and reuses 1428. All 4 are
  rc 0, with 0 errors and 0 `sorry`; sources are bound to `dfdc56f2`. State check 1432/1432 OK; the 4 rebuilt oleans have
  link count 1; snapshot #5 and the phase-2 tree both rehash 0/0/0 before, after and at the end. Only
  `BonehBoyenSecurity`'s olean changed; the 3 facade oleans are byte-identical. New output map (without `Mathlib/`):
  1463 entries, `0858dccb…`.
- **Admissions** 192, with the per-module census identical to phase 2's.
- **Axioms:** `bb1_sim_real` and `bb1_sidSecure` use only the standard three, and both `sorryAx` traces are empty; still
  76 constants, 0 non-standard. The log differs from phase 2's only in two closure sizes (15352 → 15349 and 20373 →
  20374).
- **Rule 10:** canonical coe-A on `BonehBoyenSecurity` has 2319 requests and 0 errors. The request set equals phase 2's
  exactly, because the removed `have` was not a constant. The Lean and collector logs are byte-identical to phase 2's.
  Every other owner is unchanged, so the other 35 seals and the paired controls carry over.
- **Lint:** `style_lint` 0 findings. `campaign_style_lint --check8b` gives 92 FAIL / 104 WARN, with non-INFO lines
  identical; the only INFO change is the file's line count, 225 → 223.

Then Gate 48 round 2 (Codex) at `dfdc56f2`.
