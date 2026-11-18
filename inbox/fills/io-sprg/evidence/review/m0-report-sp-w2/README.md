# M0 REPORT material

Read-only report preparation for candidate
`1a941e8ffc8f6ca5b104990f21e4bbbabecebcb0`, base
`5ed465f62e4ae0f93ded1a1ba49e807591b589eb`. This directory is staged prose/data for the
lead to integrate into the actual REPORT.md and evidence. It is not a gate result.

- `fidelity.md`: paper item/page/name/file-line/deviation mapping for all source items
  and construction components.
- `fidelity-declarations.tsv`: every lexical public declaration header; own source tags
  and prose, with glue explicitly marked. Generated declarations are the typed gate's
  responsibility. Do not treat lexical counts as decls2/StmtDump counts.
- `primitive-nonvacuity.md`: Rule-15 table, exact field-to-target selection, non-vacuity
  witnesses and shared-realiser scope.
- `helper-plan.md`: staged proof and must-reuse plan by obligation family.
- `proof-obligations.tsv`: all 146 named M0 holes and their owner proof sketches.
- `disclosures.md` and `sp-w2.md`: rational-delta ruling, acceptance-level correspondence repair, and all pre-M0 refinements/quantifier choices.
- `status-and-size.md`: measured size/widths, revised proof-completion estimate, and
  validation status carefully separated from lead-owned evidence.
- `sizes.tsv`, `source-snapshot.json`: per-file candidate SHA-256, lines/bytes/width,
  lexical declaration and hole counts.

The original independent review snapshot remains separately staged at
`/private/tmp/io-sprg-interfaces/final-draft-review.txt` and is not rebound to this
new candidate by changing its old hashes or line references. Its two chain-zero
free-program equality claims are explicitly superseded by SP-W2; use the new
acceptance correspondence in this candidate. No M0 freeze exists yet.

Only `/private/tmp` was written by the report preparers. No Lean, Lake, cache, build,
seal, axiom command, git mutation, PDF copy, or implementation source edit was run.

`make_tables.py CANDIDATE` re-extracts the lexical declarations and sizes from git show
at an explicitly selected commit; `make_proof_plan.py` refreshes the hole appendix;
`render_fidelity.py` resolves all names in the fidelity template to that inventory. Other prose contains snapshot-specific line
references and counts and must be reviewed if the source candidate changes.
