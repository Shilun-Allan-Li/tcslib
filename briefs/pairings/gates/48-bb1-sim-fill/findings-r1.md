# Gate 48 · round 1 findings (Codex), filed verbatim

Received from Seyoon in chat, 2026-11-17. The referenced `gate48-bb1-sim-evidence.zip` was linked from the auditor's
chat and was not supplied to the maintainer; this file is the auditor's Markdown summary as pasted.

---

**HOLD — 0 blockers, 1 major, 0 minors, 0 notes.**

Audited PR **#357**, Lean head `7a98ba0140ce6334bef1f2a8d39c6dfceb6ccaff`, records `e6cdf4d4eed898acd71d48bd60082140eb076cfe`, exchange `827065642ff5965c6f7c51c592f18b9f32dc2811`.

| # | Severity | File · declaration | Finding | Proposed fix |
|---|---|---|---|---|
| **G48-01** | **major** | `BonehBoyenSecurity.lean:128–134` · `bb1_sim_real`, local `h01` | The bad-coin proof re-derives the public Mathlib lemma `abs_sub_le_of_nonneg_of_le`, specialized to real numbers and upper bound `1`. This duplication is unaccepted, and the pack's assertion that no public counterpart exists is incorrect. | Remove `h01` and apply the Mathlib lemma directly. Correct the reuse claim and refresh verification at the repaired head. |

`abs_sub_le_of_nonneg_of_le` takes exactly the four bounds supplied to `h01`, in the same order, and bounds the absolute difference by their common upper bound.

This lemma exists in the **pinned** Mathlib revision `029db123ddaa7f8fd0d18cea3b1b33bf84dacd1e`: `Mathlib/Algebra/Order/Group/Abs.lean:119–124` generates it through `@[to_additive]`. The audited checkout already uses the identifier in `TCSlib/Cryptography/LWE/BitNoise.lean:110`.

The bad-coin branch can instead use:

```lean
    exact abs_sub_le_of_nonneg_of_le
      (ProbComp.prob_nonneg _ _) (ProbComp.prob_le_one _ _)
      (ProbComp.prob_nonneg _ _) (ProbComp.prob_le_one _ _)
```

This is a proposed proof-only repair, not a tested patch. DL-57 covers the `sidSpec_rng_*` twins; it does not cover this overlap. The contrary reuse claims occur in `pack-r1.md:254–255` and `fill-final-r1/review.md:218–219`. The major grading follows the gate's explicit duplication rule and Gate 44's inline-identity precedent.

The remaining audit checks passed:

| Area | Result |
|---|---|
| Integrity | **11/11** pack checksums and **189/189** verification-archive entries pass. The original phase-2 ZIP and its complete manifest also verify; I recovered its seven omitted entries. |
| Four targets | No correctness defect found. The relational induction generalizes both states; sampling reindexes along the supplied equivalence. T2 uses exactly the frozen bad event and proves identity injectivity on good coins. T3 uses the correct target-group translation. |
| Helpers and edge cases | No false, vacuous, or assumption-like helper found. All nine Step-M cases are covered, including pre-initialization calls, target-key queries, invalid/repeated challenges, and recorded challenges without an identity. Zero parameters/budgets and runs without initialization or challenge are covered. Order `1` and trivial groups are excluded by the existing bundle. |
| Frozen declarations | Independently reproduced **12/12** frozen checks, all **8** mutation controls, and **69 ADDED / 0 CHANGED / 0 REMOVED**. `bb1_sidSecure`, `prob_simulate_rel`, and the frozen sketches remain unchanged. |
| Ten readers | Both blocks are verbatim insertions at their approved anchors, retain the specified pins, restore the base exactly when removed, and reject all **12** insertion mutations. |
| LE-bsf1 | Matches the proposed diff. Apart from the added `rfl` reader `bb1RealState_eq`, all changes are comments. |
| Rule 10 | Independently recounted **36 worker head seals** and **16 base seals**, with source/probe/log bindings. Reconstructed **36/36 phase-2 seal sources** and **64/64 control sources**, matching recorded hashes and plans. Each harness has **485** sealed negatives, each failing once, and **1479** clean other entries. |
| Exceptions and unfolds | The abbrev reader's positive-only treatment and `RealReads` projection treatment satisfy the recorded rulings. The recovered scan contains **527** entries and **zero foreign definitions**; I inspected its non-theorem classes. |
| Other duplication | DL-57 records both twins, acceptance, and Stage-2 repayment. Searches across all **529** cryptography files and comparison with #355's pinned `Games/Tapes.lean` found no further undisclosed duplication. The eager/relational instances apply public framework results. |
| Sources and documentation | BB04 quotation checks match the supplied December-2004 transcription. Locators, glue notes, variant descriptions, sketches, file sizes, and widths are acceptable. |
| Replay | All **19/19** build sources and logs bind to the audited head. Recovered state contains **1432** modules; reused records are unchanged. Recorded builds have rc 0 and no error, warning, or `sorry` diagnostic. Admissions fall **196 → 192**, exactly the four targets. |
| Axioms | **76** named constants and **325** owner constants have no nonstandard axioms. All six traces are empty, including `bb1_sidSecure`'s **20,373**-constant closure. The intentional sorry control is caught by both checks. |

The prior review findings are graded separately from the new Gate-48 count:

| Review finding | Grade and disposition |
|---|---|
| BSF-F01 | Agree: minor, process only; remains disclosed. Fix future rebase/signing instructions. No history rewrite requested. |
| BSF-F02 | Agree: minor, closed by `bb1RealState_eq`. |
| BSF-F03 | Agree: minor, closed by LE-bsf1's documentation changes. |
| BSF-F04 | Regrade the pre-acceptance gap as major under the duplication rule; **closed at this pin** by Q1 and DL-57. |
| BSF-F05 | Agree: information, accepted; projections and consumer seals provide the required treatment. |
| BSF-F06 | Agree: information; the missing checkpoint acknowledgment is disclosed and resolutions are traceable. |
| BSF-F07 | Agree: information / accepted placement debt; promotion is recorded for Stage 2. |
| BSF-F08 | Agree: maintainer merge condition, outside this audit. |

I did **not** execute Lean afresh. I independently checked the static surface, regenerated probe hashes, recounted raw worker logs, and verified the recorded native-build and axiom logs. Phase-2 raw seal/probe logs remain on the maintainer host; the supplied result tables, exact regenerated sources, and worker recounts support their reported outcomes.

#351/#352 and the closed Gates 40/44 were not re-audited. No dispatch or merge was performed.
