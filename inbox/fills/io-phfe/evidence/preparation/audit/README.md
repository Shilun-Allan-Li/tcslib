# M0 fidelity, source, overlap and static-boundary audit

Prepared read-only against the managed worktree plus final stable outer-security and PHFE
agent drafts as available. No live edits, Lean/lake/build commands, source proof changes,
Git mutations or additional agents were used. All audit artifacts are under this directory.
The root is still editing; the initial machine-readable snapshot is intentionally not final
HEAD evidence and will need refreshing by root at its final checkpoint.

Read in this order:

1. **01-gjls-fidelity.md**: PRIMARY definition gate, every Def4.1/4.2/4.3/4.6 clause and
   §9 class requirement; output/allowed-value distinction, many-key quantifiers, efficiency.
2. **02-wee-fidelity.md**: §2.2 notion, assumptions, every used outer/Pi algorithm/game,
   Theorem1/Lemmas1–5, W1–W5/R1–R4, exact rank counterexample and adaptive public-fixing map.
3. **03-partial-garbling-fidelity.md**: AGW(28)–(32), IWDef1/Thm3/§4.2, specialized layered
   syntax, exact path-sum translation, dimensions, locality distinction and proof deviation.
4. **04-rule15-overlap.md**: mandatory efficiency fields/targets, uniformity, every helper
   family and nearest public TCSlib/Mathlib reuse; disclosed near-copies/promotions.
5. **05-advice-and-boundaries.md**: complete Pi/outer tape offsets and MDDH shapes, all
   realiser quantifiers/encoded-layout constraints, static scan and remaining checks.
6. **06-source-ledger.md**: verified hashes/pages and journal-consumption boundary.
7. **readers/README.md**: requested25 generic projection-reader insertion fragments and
   ML source NoScopeEscapes update. These are proposals, not inserted/Lean-checked code.

Machine-readable files from the INITIAL snapshot: snapshot.tsv (physical paths/hashes),
declarations.tsv (1,143 explicit source headers, not generated constants),
declaration-family-coverage.tsv, admissions.tsv, imports.tsv, boundary-hits.tsv,
static-summary.json. scan_static.py is a plain Python static scanner, not a proof checker.
It reports67 files/13,255 lines/145 M0 sorry occurrences at that snapshot. Do not present
these counts as a later final-HEAD census, Rule10 success or standard-axiom proof evidence.

## Findings and resolutions to retain

- Verified source-prose finding: two stale citations put Wee20 Theorem1 on p8. It is only
  AppendixB p12. Root was notified to repair before freeze; no theorem statement is false
  because of this citation error.
- Root is moving embedValue_injective into proof-only PHFE.Embedding. Its sole
  pow_val_bijective.injective use proves losslessness and never returns a scalar. Retain
  this explicit R-DLOG justification in the overlap/boundary record.
- FE agent reports the two initial >100-column Security draft lines corrected, and the
  common subexponential exponent proof route corrected to use the explicit DLIN bound
  before adversary/budget quantification.
- Fresh-vs-padded bridges now exist as substantive M0 obligations at BOTH Pi and outer
  levels. They must be proved; indexed padded endpoint equalities alone are insufficient.
- Exact unconditioned rank term replaces the source's incorrect1/p; no second rank loss.
  Polynomial column reduction contributes4d/p, already accounting for canonical DLIN's
  exceptional coordinates. Total outer matrix loss is4(ℓ+3)/p.
- Raw algorithms/security are total at zero dimensions. Only literal multiplicative
  linear-time target has the authorized positive-size guard.
- Required exact?/apply? probes, Rule10 seals/controls, StmtDump, axioms/census, final
  widths, admission check and frozen statements are still root-owned checks. Nothing
  here silently marks an unrun check passed.

No new false/vacuous mathematical statement was found in the reviewed source clauses,
game formulas, advice coordinates, target quantifiers or machine-derived realizability
premises. This finding is a static review conclusion; it does not establish the many
admitted M0 correctness/security/endpoint-law theorems.
