# Gate 07 (equation-lemma PR #210): round 2 resolutions

- **Round 2:** findings `findings/gate07-eqlemmas-r2-findings.md`, verbatim (delivered by upload; no copy in the exchange
  inbox), SHA-256 `e3cd0b7927f9bb30d743c80499eaa4f86f64bc0bc34340edc98d1193f7a5cfc6`; head `3436321ba28042549bead976dc654aab3d661f10`.
  **Verdict HOLD: 0 blockers, 1 major (R2-01), 2 minors (R2-02, R2-03).** F01 and F03 fixed; F02 not resolved
  (R2-01). The auditor found no counterexample to the new equations, no mathematical change in the restatements,
  and no further rule-10 read in a touched declaration; it reproduced the 547-declaration touched list and the
  (a) = 0 / (b) = 764 classification from the evidence, and checked 781 declaration headers against source.

| Finding | Severity | Resolution |
|---|---|---|
| R2-01 | major | **Confirmed.** No probe consumed `PermCollection.glPad_domEquiv` / `_apply` / `glPad_perm` from another file with `PermCollection.glPad` and `Collection.glPad` sealed; round 1's resolution claimed it. **Repair:** a pass probe that states the conjugated permutation equation on `(P.glPad m henc).D i` through `P.glPad_domEquiv` (and the domain/application lemmas), sealed with `PermCollection.glPad`, `Collection.glPad` and every foreign definition they reach; a paired control that reads the product domain/permutation directly and passes unsealed, fails sealed; source-to-log mapping; at #210's head. F02's disposition is corrected only then. |
| R2-02 | minor | **Confirmed.** `invProb_def`, `predProb_def`, `acceptProb_def`, `distAdv_def`, `invProbOpt_def`, `glPadInvFun_eq`: docstrings get the formula. Docstring-only. |
| R2-03 | minor | **Confirmed.** (1) The `sorry` attestation named the wrong baseline: against the PR base `05fe903f`, Factoring 8 → 10 and RSA 9 → 10 (exactly S1–S3); the round-5 comparison was against `16a7d02d`. A base comparison is regenerated and the wording corrected. (2) `decls.py` stops a statement at a `|` line even inside a statement-level `match` (`GGMRed.queryOf_eq`); the extractor is fixed to continue through match arms before the declaration's `:=`, and the tables are regenerated. |

Round 3 checks R2-01–R2-03 only.
