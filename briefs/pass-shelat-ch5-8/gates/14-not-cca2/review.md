# not-cca2 · maintainer delivery review (round 2 final)

**Verdict: ACCEPT WITH LANDING EDITS** (0 blockers, 0 majors, 4 minors, 3 notes).

Delivery: round 1 Codex (checkpoints 1–2, escalation), round 2 Claude, exchange `b7604844`
(`inbox/fills/not-cca2/`); 3 patches on `4a09f3993eb9344fc5714610e41ab141a0144db8`. Independent
review on a landing branch on the post-#286 head; evidence `review-evidence.zip` (SHA-256 `27ba267b220c4b3cf842606b4e9d1fcf73ab4423b30fdddcfda4287365104439`;
inner `SHA256SUMS` 364 files, pins in `PROVENANCE.txt`).

## Checks (re-run by the reviewer)
- Integrity: payload sums 429/429; `git am` reproduces `src/` byte for byte.
- Landing build (fresh tree, `fillinputs.py` order of 238 modules): 238/238 rc 0, 0 errors.
- Admissions: landing parent 32 → head 31; only `prfFixedScheme_not_cca2` removed.
- Statements: 0 changed, 0 removed; 7 public added (`prfScheme_dec`, 6 readers).
- Axioms: target, corollary, `prfScheme_dec` and readers standard; over all 218 stored constants
  of the three modules only `_cpa`/`_cca1` carry `sorryAx`.
- Rule 10: whole-file closure seals (1754 / 678 / 1842 requests) 0 errors; base seals 0 errors;
  6 control probes ALL_OK; explicit-reader scan 318 items, 0 foreign.
- Lint 0 FAIL (same 5 WARN as base).

## Findings and dispositions
| # | Severity | Finding | Disposition |
|---|---|---|---|
| 1 | minor | Stale module docstring in `OracleFromPRF.lean` ("stated; a `sorry`"). | **Landing edit.** |
| 2 | minor | Stale facade docstring `PrivateKey.lean` ("also pending"). | **Landing edit.** |
| 3 | minor | Dead round-1 helper `cca2Unmask`. | **Landing edit:** deleted. |
| 4 | minor | `cca2OfFn_padFin` duplicates `GGMRed.ofFn_padFin_of_length`. | **Landing edit:** replaced; DL-31 tracks the shared home. |
| 5 | note | Reader set omits `indImpl_challenge_repeat_onSpec`/`_enc_onSpec` (unused). | Consistent with the brief; `_repeat_onSpec` deferred to the `_cpa`/`_cca1` fills. |
| 6 | note | `indImpl_dec_onSpec` casts the answer (unlike the public-key file). | Correct form for sealed consumers; kept. |
| 7 | note | Patch 3 titled "r2 checkpoint 1" holds the final content. | Recorded; history kept as delivered. |

## Landing
Branch `land/pass-shelat-not-cca2` at `7960d6d4c3254797fdec191fff72c8d4c0147e1a` (3 delivered commits +
landing edits) on the post-#286 head. After the edits: the 4 affected modules rebuilt (0 errors),
downstream through `TCSlib` and `audits/pass-shelat/Checks` (18 modules) rc 0 on the full tree,
axioms standard (`landing/`). PR #289 (draft).
