# adaptive-cpa · maintainer delivery review (r1)

**Verdict: ACCEPT WITH LANDING EDITS** (0 blockers, 0 majors, 4 minors, 5 notes).

Delivery: Claude worker, exchange `35b16407` (`inbox/fills/adaptive-cpa/`), 5 patches on
`4a9b2c91eb2f89c4fb624339d5b4ba9cfd35ac27`. Independent review on the landing branch (parent =
campaign after #289); evidence `review-evidence.zip` (SHA-256 `0a4c83d499d7c5b355327af61eeb60e3df8154142e9afceec63b44b4c742e976`; `PROVENANCE.txt`, inner
`SHA256SUMS` 357 files).

## Checks (re-run by the reviewer)
- Integrity: payload sums 487/487; `git am` reproduces `src/` byte for byte (1 modified, 4 added).
- Build: 201-module closure (issued 197 + 4 helpers, 92 roots) 201/201, 0 errors, fresh tree.
- Admissions: issued base 27, landing parent 26 (#289), head 25: only `INDSecure.adaptive_cpa` removed.
- Statements: 69 ADDED, 0 CHANGED, 0 REMOVED.
- Axioms: `adaptive_cpa` and all 175 stored constants of the five modules standard;
  `bitwise_padded_adaptive_cpa`/`exists_adaptive_cpa` carry `sorryAx` via the bitwise target.
- Rule 10: whole-file closure seals of all five files (685 / 2,125 / 2,167 / 2,172 / 2,174 requests)
  PASS; base control PASS; 10 control probes, 55 negatives ALL_OK; explicit-reader scan 627 items,
  0 foreign. Lint 0 FAIL (same 6 WARN as base).

## Findings and dispositions
| # | Severity | Finding | Disposition |
|---|---|---|---|
| 1 | minor | Stale "stated; a `sorry`" in `AdaptiveCPA.lean`; facade lacks `## Contents`. | **Landing edit.** |
| 2 | minor | Private `Handler.pairEncode_append` copies `GGMRed.pairEncode_append_right` (report said no duplication). | **Landing edit:** removed and re-pointed. |
| 3 | minor | Nine lemma docstrings without their formula (Hybrid, Games). | **Landing edit.** |
| 4 | minor | Unused simp argument (`Handler.lean:266`). | **Landing edit.** |
| 5 | note | Public `AdaptiveCPA.ofFn_cast` = private `cca2OfFn_cast` (#289, landed after the issue base). | New ledger row DL-32. |
| 6 | note | Generic material to promote: `expect_sample_update` (Probability), `simulate_eq_of_abs` and the `castImpl` family (Simulate), `padFin_ofFn_zeroBits`, `headD_ofFn_one`, `ofFn_splitHalf_fst/_snd`; reader request `indCodec_eq_bitCodec`; new uses of `GGMRed.ofFn_padFin_of_length`. | Added to DL-30 / DL-31 follow-up. |
| 7 | note | `Handler.lean` 601 lines (596 after edits). | No action. |
| 8 | note | Proof and API review: no defects (hybrid endpoints, handler equations and poly proof, state abstraction, eager/lazy tapes, bound incl. cap 0, edge cases). | — |
| 9 | note | Downstream: `BitwiseCPA`, facades, root; `Checks` does not import it. | Root/Checks run by the maintainer. |

## Landing
Branch `land/pass-shelat-adaptive-cpa` at `95df0b4fa15e140ffd8f692699c66d0683fc916d` (5 delivered commits +
landing edits). After the edits: 8 affected modules rebuilt (0 errors); 22 modules through
`TCSlib` and `audits/pass-shelat/Checks` rc 0 on the full tree (`landing/`). PR #290 (draft).
