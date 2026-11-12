# pk-cpa-cca1 · maintainer delivery review (r1)

**Verdict: ACCEPT WITH LANDING EDITS** (0 blockers, 0 majors, 1 medium, 4 low, 6 info).

Delivery: Claude worker, exchange `5285ea8a` (`inbox/fills/pk-cpa-cca1/`), 8 patches on
`8c3afbff69ad1273446750f47c05d424ab13ebe2`. Independent review on the landing branch (parent = campaign
`ce22c4da`, 0 Lean changes since the base); evidence `review-evidence.zip` (SHA-256 `f36b9eaa624883fa030435f888b17cca5f93dbb30e52f6e61b93af1d818570ab`;
`PROVENANCE.txt`; inner `SHA256SUMS` 527 entries).

## Checks (re-run by the reviewer)
- Integrity: payload sums 101/101; `git am` reproduces `src/` and the worker's tree.
- Build: the `PrivateKey/OracleSecurity` closure plus downstream (251 modules; the issued order missed the two
  Implications modules) 251/251, 0 errors; touched modules 0 warnings.
- Admissions 29 → 27 (exactly the two targets). Statements: 134 ADDED, 0 CHANGED, 0 REMOVED; the four
  OracleSecurity readers match the brief's names and the `_onSpec` form.
- Axioms: both targets, `not_prfFixedScheme_cca2`, and all 434 stored constants of the 8 modules standard.
- Rule 10: whole-file closure seals 8/8 (678–2,281 requests) with base controls; 16 probes, 226 negatives
  ALL_OK; explicit scan 1,376 items, 0 foreign. Lint 0 FAIL (same 5 WARN as base).
- The worker's deviations (one reduction per bit; bound `prfAdv(D₀)+prfAdv(D₁)+(q²+1)2⁻ⁿ`) are sound and
  within the brief; `q²` is needed because later encryptions can hit `r*`.

## Findings and dispositions
| # | Severity | Finding | Disposition |
|---|---|---|---|
| 1 | medium | `PRFGame.toComp_costBoundedBy` copies `NUPPT.toComp_costBoundedBy`. | **Landing edit:** removed, re-pointed. |
| 2 | low | `PRFGame.eq_of_ofFn_eq` = `List.ofFn_injective`. | **Landing edit.** |
| 3 | low | Prose-only lemma docstrings (Collision, Lazy, Transfer). | **Landing edit:** formulas added. |
| 4 | low | Long proofs without sketches (Handler, Collision, Lazy). | **Landing edit:** sketches added. |
| 5 | nit | Three lines over 100 characters. | **Landing edit.** |
| 6 | low | Undisclosed copies of private AdaptiveCPA handler pieces in `Handler.lean`; `ofFn_pkTapes` re-proves `ofFn_acTapes`. | Ledger DL-34. |
| 7 | info | Private-key `indCodec_eq_bitCodec`; `mem_keys_of_lookup_isSome` near core. | Ledger DL-34. |
| 8 | info | `fImpl` docstring said "oracles of IND_b" without the attack qualifier. | **Landing edit:** "under CPA and CCA1". |
| 9 | info | Public `abbrev LState` has no `_eq` lemma. | No action (abbreviation). |
| 10 | info | The worker's reported seal failure came from sealing `PolyExpr.eval` (notation by ruling). | No action. |
| 11 | info | Bound soundness confirmed. | — |

## Landing
Branch `land/pass-shelat-pk-cpa-cca1` at `63ca0eb3dccb65542e90c181b7ceb0a4a4a46272` (8 delivered commits + landing
edits). After the edits: 10 affected modules rebuilt (0 errors, hash-bound); 28 downstream modules through
`TCSlib` rc 0 on the full tree (`landing/`). PR #293 (draft).

## Errata (after Gate 17)
- Item 9 was wrong: policy §1 requires an `_eq` lemma for a new public `abbrev`. `LState_eq` was added (G17-01).
- "`q²` is needed" overstated the point: later encryption collisions make the query-by-query quadratic bound the
  natural one, but its necessity was not shown (Gate 17 remark).
