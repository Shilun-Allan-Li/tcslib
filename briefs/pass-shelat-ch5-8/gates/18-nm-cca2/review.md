# nm-cca2 · maintainer delivery review (r1)

**Verdict: ACCEPT WITH LANDING EDITS** (1 high fixed by a landing edit, 1 medium-low, 3 low, 2 nit, 3 info;
no blockers remain after the edits).

Delivery: Claude worker, exchange `906f47381f5fdf677d88397251dd737c125e4bfb` (`inbox/fills/nm-cca2/`;
checkpoints `f3878eb2b`, `bd936f02c`), 4 patches on the issue base
`b96ab3ccc1915497ea3138df499eec00b6581db0`. Independent review on the landing branch (parent = campaign
`71da4e6a`, 0 Lean changes since the base); evidence `review-evidence.zip` (SHA-256
`fc321bfb04a7fc821da569bf2d56412fa64f70acb02565ad2d21dffbe3948c29`; `PROVENANCE.txt`; inner `SHA256SUMS`
635 entries, SHA-256 `002d52707ecf1e6db2a2d59b39b0423b7feed15150389e365685ac8abf22b55f`).

Target: [PS10, Theorem 175.9], `FixedLengthPKScheme.indSecure_cca2_iff_nmSecure_cca2`
(`PublicKey/NonMalleability/Indistinguishability.lean`), proved with helpers
`Indistinguishability/{Forward, Decrypt, Encrypt}.lean` (and `Readers.lean`, removed at landing).

## Checks (re-run by the reviewer)
- Integrity: payload sums 625/625; `git am` at the issue base reproduces the worker's proof-branch tree
  `746ec283e9e6…`; the 5 files are byte-identical to `src/`.
- Build: the fill closure plus downstream (253 modules = issued 249 + the 4 helpers), fresh tree, 253/253,
  0 errors.
- Admissions 27 → 26 (exactly the target). Statements: 64 ADDED, 0 CHANGED, 0 REMOVED.
- Axioms: the target and both directions `[propext, Classical.choice, Quot.sound]`; all 170 stored constants
  of the 5 files standard. `simNMSecure_cpa_iff_nmSecure_cpa` still carries `sorryAx` (the two open
  `Simulation.lean` targets), as at the base.
- Rule 10: whole-file closure seals, variant A (`PolyExpr.eval` exempt as notation) and B (sealed): the owned
  file, Forward, Decrypt and Encrypt pass both; `Readers.lean` fails each with exactly one error, at
  `indImpl_dec_onSpec_cast` (the disclosed exception). Controls: 20 probes, ALL_OK in both variants (67/72
  sealed negatives fail exactly once). Explicit scan 526 items, 0 foreign. Lint 0 FAIL (same 6 WARN as base).
- E-READER confirmed independently: with only `outLens` sealed, four routes to the cast form each leave
  `decAnswer X = cast _ (decAnswer X)`; unsealed, the one-line proof passes. No published reader closes it.

## Findings and dispositions
| # | Severity | Finding | Disposition |
|---|---|---|---|
| 1 | high | E-READER: no cast-form reader of the `Dec` answer in `PublicKey/OracleSecurity.lean`; the helper `Readers.lean` reads `outLens`. | **Landing edit LE-1:** `FixedLengthPKScheme.indSpec_decRng` and `indImpl_dec_onSpec_cast` added beside `indImpl_dec_onSpec`; `Readers.lean` and its import deleted; `castImpl_indImpl_dec` re-pointed. Both readers pass seals A and B in their home file. |
| 2 | low | Owned module title still "(statement phase)". | **Landing edit LE-2.** (`Simulation.lean` keeps it: still sorried.) |
| 3 | nit | Two doubled blank lines in the owned file. | **Landing edit LE-3.** |
| 4 | medium-low | `logEmit` (`Forward.lean`) generalizes `Games.EffFill.relabelN`/`relabel` (`Games/Efficiency/OracleBridge.lean`); its log lemmas mirror `relabelN_encodeHist`, `length_le_length_encodeHist` and the orbit bound of `bridgePre_poly`. Not disclosed. | Ledger **DL-36**; promotion redirected beside `relabelN`. |
| 5 | low | Public `finU`…`finL`, `fields_finInput` repeat the DL-34 round-input readers (`rU`…`rL`). | Ledger **DL-36**; re-point to consolidation R6. |
| 6 | low | `ofFn_nthCt` is the generic block fact of DL-34 (`ofFn_acTapes`, `ofFn_pkTapes`). | Ledger **DL-36**. |
| 7 | nit | Label-only docstrings: `polyTimeComputable_cntRead`, `_ansRead`, `_finFields`; `finZ`…`finL`. | **Landing edit:** formulas added to the three; the readers go with finding 5. |
| 8 | info | REPORT says two names re-point in `castImpl_indImpl_dec`; only one does. | No action. |
| 9 | info | The owned file uses `ChallengeSim.expect_sample_*` and `AdaptiveCPA.castImpl*`, which the consolidation moves; its opens should keep them resolving. | Consolidation landing rebuilds and re-points (land-order ruling 2026-11-12). |
| 10 | info | Proof review of both directions, the handlers, finalization, budgets and edge cases (budget 0, ℓ = 0, no or repeated challenge, timeout, `msgLen = 0`): no issues. | — |

**Promotion requests** (worker): accept `fwdHandler`/`_impl` and `exists_withAdviceOn` (→ `Games/Efficiency`),
`cntRead`/`ansRead` (→ `BitCodec`); `logEmit` per finding 4; `finU`…`finL` per finding 5;
`indImpl_eq_of_msgLen_eq_zero` (→ `OracleSecurity`) waits for the split below. All in DL-36.

**Size.** `PublicKey/OracleSecurity.lean` goes 982 → 999 lines (limit < 1000). No headroom: the consolidation's
readers R1, R3, R4 for this file need the split first. Recommended split (reviewer): move `section PaddedCPA`
(297 lines, self-contained; consumers `TrapdoorCPA.lean` and the facade docstring; the `ChallengeSim`/
`RecordHandler` imports go with it) to `PublicKey/OracleSecurity/PaddedCPA.lean`. Scheduled as a landing edit
of the consolidation.

## Landing
Branch `land/pass-shelat-nm-cca2`, rebased onto campaign `4d10bc4e5` (records-only since `71da4e6a`): the 4
delivered commits + landing edits `1636480237286f538bb75b0021b2285edcd0b5b9`. After the edits: the 29 modules
downstream of `OracleSecurity` and the fill (through `TCSlib`) rebuilt on the full tree, hash-bound
(`landing/`). `audits/pass-shelat/Checks` imports none of these modules.
