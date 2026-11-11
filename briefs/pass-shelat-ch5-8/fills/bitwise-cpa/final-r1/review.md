# bitwise-cpa · maintainer delivery review (r1)

**Verdict: ACCEPT WITH LANDING EDITS** (0 blockers, 0 majors, 2 medium, 3 low, 3 info).

Delivery: Claude worker, exchange `4aa36699` (`inbox/fills/bitwise-cpa/`), 3 patches on
`4a9b2c91eb2f89c4fb624339d5b4ba9cfd35ac27`. Reviewed on a landing branch stacked on #290
(`land/pass-shelat-adaptive-cpa` at `95df0b4f`); evidence `review-evidence.zip` (SHA-256 `d3fd1750ace71d0111c0415fc823b728ae574df50f8fbb4a0f1a238e59b69ca4`;
`PROVENANCE.txt`, inner `SHA256SUMS` 380 files).

## Checks (re-run by the reviewer)
- Integrity: payload sums 63/63; `git am` reproduces `src/` byte for byte.
- Build: 204-module closure, fresh tree, 204/204 rc 0, 0 errors.
- Admissions: issued base 27 → landing parent 25 → head 24 (removed `prfFixedScheme_not_cca2` by #289,
  `adaptive_cpa` by #290, `bitwise_padded_cpa` here; none added).
- Statements: 43 ADDED, 0 CHANGED, 0 REMOVED (plus `simps` readers of `qHandler`; 13 private).
- Axioms: `bitwise_padded_cpa`, `bitwise_padded_adaptive_cpa`, **`exists_adaptive_cpa`**,
  `adaptive_cpa` and all 97 stored constants of the four modules standard.
- Rule 10: whole-file closure seals of the four files (2,021 / 2,125 / 2,125 / 2,185) rc 0; base
  control rc 0; 8 control probes, 60 negatives ALL_OK; explicit-reader scan 412 items, 0 foreign.
- Lint 0 FAIL (same 6 WARN as base).

## Findings and dispositions
| # | Severity | Finding | Disposition |
|---|---|---|---|
| 1 | medium | `BitwiseSim.ofFn_cast`, `BitwiseSim.indCodec_eq_bitCodec` duplicate the parallel adaptive-cpa fill's lemmas. | **Landing edit:** removed; uses re-pointed to `AdaptiveCPA.*`. |
| 2 | medium | `Planted.lean` 152 s, almost all in three `convert … using 1` blocks. | **Landing edit:** `PolyTimeComputable.congr`; 2.4 s. |
| 3 | low | Docstrings without formulas (QueryHandler, Planted, Eager). | **Landing edit.** |
| 4 | low | Facade lacks `## Contents`. | **Landing edit.** |
| 5 | low | Three lines over 100 characters. | **Landing edit.** |
| 6 | info | Promotion and duplication candidates: two forms of `expect_sample_update`; generic eager-coins lemma vs the private one in `OracleSecurity`; `chRun_toCompOn_transport_list` generalizes `ChallengeSim`'s; list lemmas `headD_drop`, `flatten_ofFn_singleton` (copies elsewhere); `decodeFin_nil_getD`; `padded_enc_runAt/_coins`; a third copy of the two-oracle length-vector pattern; new DL-31 uses; small private re-proofs; reader request `HybridMachine.hybridPre_eq`. | Ledger row DL-33. |
| 7 | info | Proof and API review: no defects (hybrid endpoints, `n = 0`, handler, advice length, planted layout, signed identity, bound, edge cases). | — |
| 8 | info | No separate checkpoints 2–3 (checkpoint 1 already had the full proof); the worker's own seal was root-scoped, the review's closure seals are stronger. | Recorded. |

## Landing
Branch `land/pass-shelat-bitwise-cpa` at `c286bc6a9b372036f959a033729d841ce10dfa16` (on #290's branch; 3 delivered
commits + landing edits). After the edits: 6 affected modules rebuilt (0 errors, 0 warnings); downstream
through `TCSlib` rc 0 on the full tree (`Checks` does not import these modules). PR #291 (draft, base
#290's branch).
