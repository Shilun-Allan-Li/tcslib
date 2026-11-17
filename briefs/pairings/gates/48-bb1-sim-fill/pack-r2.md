# Gate 48 · the bb1-sim gate (#357) · round 2 · G48-01 fixed by LE-g48

Round 1 (Codex) was **HOLD**: 0 blockers, 1 major (G48-01), 0 minors, 0 notes, and no mathematical gap
(`findings-r1.md`). The maintainer's resolution is `resolutions-r1.md`: **landing edit LE-g48**, the fix Codex proposed.

| Item | Pin |
|---|---|
| PR #357 head, round 2 | `dfdc56f21898abe2d9d6cef83b0cfe57da87d28d` (round 1's head `7a98ba0140ce6334bef1f2a8d39c6dfceb6ccaff` + LE-g48) |
| Records, round 1 | `e6cdf4d4eed898acd71d48bd60082140eb076cfe` |
| Records, round 2 | given in the dispatch prompt (the commit that files this pack) |
| Round-1 pack | exchange `827065642ff5965c6f7c51c592f18b9f32dc2811`, `outbox/gates/48-bb1-sim-fill-gate/` |

This folder supersedes an earlier round-2 pack at exchange `5976f1a0`, which was staged on Seyoon's first ruling
(accept as debt, DL-58) and **never dispatched**. Seyoon then asked for the fix before round 2.

## 1. LE-g48 (G48-01)
- **Commit** `dfdc56f2`, sole parent `7a98ba01`, SSH-signed with the records key (`SHA256:32dP45eS…2wc`, as
  `7a98ba01`), message ending with the two trailers.
- **Diff** (`le-g48.diff.txt`; `git diff 7a98ba01 dfdc56f2`): one file, `BonehBoyenSecurity.lean`, 1 line added and 3
  removed. The local `have h01 … := fun x y _ _ _ _ => abs_sub_le_iff.2 ⟨by linarith, by linarith⟩` (2 lines) is
  deleted. The bad-coin branch's `exact h01 _ _ (…) (…)` becomes
  `exact abs_sub_le_of_nonneg_of_le (ProbComp.prob_nonneg _ _) (ProbComp.prob_le_one _ _)`; its continuation line
  `(ProbComp.prob_nonneg _ _) (ProbComp.prob_le_one _ _)` is unchanged. `h01` occurred nowhere else: not in the
  docstring, the proof sketch or a comment. The "bad coins: two probabilities differ by at most `1`" comment stays true.
- **Records:** ledger row DL-58 is kept and marked **repaid by LE-g48**. Its Stage 2 line in `cleanup-stages.md` is
  struck. The phase-1 review's wrong reuse claim keeps its text, with the dated correction and an update beneath it. The
  plan's decision log records both rulings: first debt, then the fix. #357's description records LE-g48
  (`pr357-description-r3.md`, as sent).
- `records-r1-r2.diff.txt` is `git diff e6cdf4d4 <round-2 records>` over the ledger, `cleanup-stages.md`, the fill
  review and the plan. The ledger hunk also contains an earlier records-only fix, disclosed in round 1's slips: a
  five-column header above DL-30, and DL-57's line refs corrected to `:77`/`:84`.

## 2. Evidence at `dfdc56f2` (`le-g48.md`, `le-g48-evidence.zip`)
- **Replay** on a `cp -al` copy of round 1's phase-2 output (`olean-replay-bb1sim` → `olean-replay-bb1sim-g48`). With
  phase 2's state and order files, the plan builds 4 modules (`BonehBoyenSecurity` and the `IdentityBased`,
  `AdvancedEncryption` and root `TCSlib` facades) and reuses 1428. All 4 built through the recipe's `runner.py` with
  rc 0, 0 `error:`/`error(` and 0 `sorry`. Sources are bound to `dfdc56f2` 4/4.
  - State check 1432/1432 OK; exactly the 4 rebuilt oleans have link count 1.
  - Snapshot #5 and the phase-2 tree both rehash 0/0/0 before, after and at the end.
  - Only `BonehBoyenSecurity`'s olean changed; the 3 facade oleans are byte-identical. New output map 1463 entries,
    `0858dccbee016da1da450f2b2ca0d1f5094ee42646b9496d5278f2b45cb07caf`.
- **Admissions:** 192, with the per-module census identical to phase 2's.
- **Axioms** (phase 2's probe): `bb1_sim_real` and `bb1_sidSecure` use only `propext`, `Classical.choice` and
  `Quot.sound`, and both `sorryAx` traces are empty. Still 76 constants, 0 non-standard. The log differs from phase 2's
  only in two closure sizes: `bb1_sim_real` 15352 → 15349 and `bb1_sidSecure` 20373 → 20374.
- **Rule 10:** canonical coe-A on `BonehBoyenSecurity` with phase 2's harness has 2319 requests and 0 errors. The
  request set equals phase 2's exactly, because the removed `have` is not a constant. The seal's Lean log and the
  collector log are byte-identical to phase 2's; the seal JSON differs only in rev, hashes and offsets. No other owner
  changed, so the other 35 seals, the paired controls and the unfold scan carry over.
- **Lint:** `style_lint` 0 findings. `campaign_style_lint --check8b` gives 92 FAIL / 104 WARN, with non-INFO lines
  identical to phase 2's; the only INFO change is the file's line count, 225 → 223.

## 3. Questions for the audit
1. Is G48-01 closed by LE-g48: is the edit exactly the stated proof-only change, does it use the Mathlib lemma
   correctly, and does nothing else change?
2. Does the evidence bind to `dfdc56f2` and support compilation, admissions, axioms and the seal? Is carrying over round
   1's other seals, controls and unfold scan justified for this delta?
3. Are the records (DL-58 marked repaid, the struck Stage 2 line, the review correction, the PR description) accurate?
4. Is anything new undisclosed?

## 4. What does not change
Every round-1 pass stands for the unchanged 8 files and the rest of `BonehBoyenSecurity.lean`. Out of scope as before:
#351/#352 (DW-11), Gates 40 and 44, and merge order and snapshot adoption (maintainer conditions; the snapshot-#6
candidate is now `olean-replay-bb1sim-g48`).

## 5. Findings delivery
Return `gate48-bb1-sim-r2-findings.md` as Markdown in chat: findings G48-02 onward if any, counts by severity, and a
verdict: CLEAR (zero blockers and zero majors) or HOLD.
