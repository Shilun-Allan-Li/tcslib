# Gate 109 (#218, B6's H landing): resolutions

## Round 1 findings (received 2026-11-06)

`findings.md`, verbatim (SHA-256
`ecbe4a8fc7a79a6aff8421437bd9dfafd61f148e8fc3a6e6bd37f48a44a5800d`). **Verdict: PASS at
`65d72947`: 0 blockers, 0 majors, 4 minors, 7 notes.** No soundness defect was found, and E-PAD
remains the authorized admission. **The gate is CLOSED.**

| # | Severity | Disposition |
|---|---|---|
| 1 | minor | **Fixed** (`1a782c36`; the standing rule, WORKFLOW §3). All six conversions cite `Cfg.mapState_eq_of_fields`, keeping their field proofs: `sph_rewinds_run`'s `hend`, both branches of `sph_verdict_run`, `sph_valid_machine`'s `hstart`, `sph_validated_machine`'s `hstart₁` and `hpre`. The ledger's RN-1 records them as retired in #218. The sweep's and the delivery classification's "idiom" dispositions for those pairs are superseded here. The file elaborates (2 `sorry` warnings, as before). The seal, freeze, lint, screen and a replay on the campaign after #211 are regenerated at the new head (`evidence/round1-fixes/`). |
| 2 | minor | **Accepted.** The head lint log was generated from the pre-#216 tree. It is regenerated from a clean `git archive` of the new head (`evidence/round1-fixes/lint/`). |
| 3 | minor | **Accepted** as a REPORT erratum. Checkpoint 7 proves `LOGSPACE_ssubset_PSPACE` conditional on `space_hierarchy`. It becomes admission-free at checkpoint 6's later commit `37a041bc`. The raw log is `evidence/logs/cp7-discover/002-FillProbes_cp7_Axioms.log`. Checkpoint numbers are not commit order. |
| 4 | minor | **Waived by the maintainer.** The separate checkpoint zips are not required for this gate. The final archive (965 entries verified), the eight-patch chain and the git bundle reconstruct every checkpoint source, as the auditor confirmed. |
| 5–11 | note | No change. Note 11's post-#217 replay is done (`replay-lh3`, on the campaign after #211). |
