# Gate 48 · the bb1-sim gate (#357) · round 2 · G48-01 resolution only

Round 1 (Codex) was **HOLD**: 0 blockers, 1 major (G48-01), 0 minors, 0 notes, and no mathematical gap
(`findings-r1.md`). The maintainer's resolution is `resolutions-r1.md`. **The code is unchanged.**

| Item | Pin |
|---|---|
| PR #357 head | `7a98ba0140ce6334bef1f2a8d39c6dfceb6ccaff`, the same as round 1 (live `land/pairings-bb1-sim` checked at staging) |
| Records, round 1 | `e6cdf4d4eed898acd71d48bd60082140eb076cfe` |
| Records, round 2 | `8780fb1d7dbbb230d26a15a5240baf4f7a113008` |
| Round-1 pack | exchange `827065642ff5965c6f7c51c592f18b9f32dc2811`, `outbox/gates/48-bb1-sim-fill-gate/` |

## 1. G48-01 (major): the resolution
**Ruling (Seyoon, 2026-11-17): accept as debt.** The alternative offered was a landing edit plus a replay; Seyoon chose
the debt route of the Gate 44 G44-01 precedent. The overlap is retained and recorded as follows:
- **Ledger row DL-58** (`briefs/pass-shelat-ch5-8/duplication-ledger.md`):
  - new declaration: `bb1_sim_real`'s local `h01` (`BonehBoyenSecurity.lean:128–134`);
  - existing copy: Mathlib `abs_sub_le_of_nonneg_of_le` (`Mathlib/Algebra/Order/Group/Abs.lean:119–124`, additive form,
    pinned `029db123`), already used in `LWE/BitNoise.lean:110`;
  - status: accepted by Seyoon, 2026-11-17, ruling G48-01;
  - repayment: **cleanup Stage 2**, delete `h01` and apply the Mathlib lemma to the four
    `ProbComp.prob_nonneg`/`prob_le_one` bounds (proof-only).
- **Stage 2 scope** (`briefs/pass-shelat-ch5-8/cleanup-stages.md`): one new line naming DL-58 beside DL-55–DL-57.
- **The review's wrong claim** (`fills/bb1-sim/fill-final-r1/review.md`, § Duplication and reuse): the text is kept, and
  a dated correction directly beneath it says the claim was wrong, why the search missed it (Mathlib's generic `abs`
  lemmas were not covered), and names DL-58.
- **The round-1 pack** (`pack-r1.md:254–255`) stays as filed; this round-2 pack supersedes its reuse claim.
- **PR #357's description** now has a DL-58 bullet under "Overlap and reuse" and a "Gate 48" section stating round 1's
  verdict (`pr357-description-r2.md`, as read back after the update).
- **Decision log:** the row of 2026-11-17 in `PairingCryptographyPlan.md` ("Gate 48 round 1 (Codex): HOLD … DL-58").

`records-r1-r2.diff.txt` is `git diff e6cdf4d4 8780fb1d` restricted to those four records files. The ledger hunk also
contains an earlier records-only fix made after the round-1 pin was taken and before this round: a five-column header
inserted above DL-30 (rows DL-30 onward had five cells under a four-column header) and DL-57's line references
corrected from `:78`/`:85` to `:77`/`:84`. Round 1's pack disclosed both slips.

## 2. Question for the audit
Does the resolution of G48-01 meet `policy.md` §1 for an accepted duplicate: Seyoon's explicit acceptance, the shared
home (here Mathlib), and a recorded repayment point? Is G48-01 closed?

## 3. What does not change
The head is unchanged, so every round-1 pass stands: the four targets, the helpers and edge cases, the frozen checks,
the ten readers, LE-bsf1, Rule 10, the unfold scan, the other duplication checks, sources, the replay and the axioms.
Nothing is re-run and nothing needs re-auditing. Out of scope as before: #351/#352 (DW-11), Gates 40 and 44, and merge
order and snapshot adoption (maintainer conditions).

## 4. Findings delivery
Return `gate48-bb1-sim-r2-findings.md` as Markdown in chat: findings G48-02 onward if any, counts by severity, and a
verdict: CLEAR (zero blockers and zero majors) or HOLD.
