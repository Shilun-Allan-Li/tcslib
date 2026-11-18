## Size re-estimate and validation status

Candidate `1a941e8ffc8f6ca5b104990f21e4bbbabecebcb0` has 22 new Lean files, 5,899
lines and 300,480 UTF-8 bytes. The largest line is 100 characters. There are 146 named
M0 proof obligations, all with an owner-side Proof sketch. `sizes.tsv` records every
file's line/byte/width counts and SHA-256. The root `TCSlib.lean` import addition is
the one permitted existing-file change and is not included in the new-file total.

The textual public-header inventory has 674 rows: 670 named headers and four
anonymous-instance positions. This is not an elaborated declaration count: generated
structure/instance/projection declarations are accounted for by the lead's typed
StmtDump and decls2 outputs, not by this lexical table.

The initial 4,950–8,450-line expectation leaves about 2,600 lines above this M0.
Filling 146 holes within that upper estimate would allow only about 17 added lines
per hole on average. The main unknowns are rounding/stretch asymptotics, Claim4.2's
conditional product estimates and exponential absorption, and the typed hybrid
averaging/coin transports. A cautious revised completion estimate is roughly
8,500–11,500 Lean lines, including genuinely missing helper proofs and reader glue.
This is an estimate, not an expansion of scope. Keep each file below 1,000 lines;
if a proof-heavy owner approaches that limit, split supporting helpers into a new
inner-namespace module and disclose that import refinement before using it.

This subagent performed only read-only source inspections, targeted text searches,
and deterministic Python inventory/size/docstring checks. It did not run Lean,
Lake, a cache fetch, canonical seals, paired controls, axiom probes, full lint,
clash scan, decls2, or StmtDump for this report task. The lead is collecting those
M0 gate artifacts and must fill the validation table from the actual logs.

| Evidence item | Status in this report material |
| --- | --- |
| Source PDF hash | Lead verified the expected hash before reading; source was read in place, never copied. Hash log is owned by the lead. |
| Source inventory / widths | Independently measured at the stated candidate; all 22 new files, maximum width 100. |
| Fidelity / rule 15 / non-vacuity | Source-level tables incorporate the SP-W2 acceptance repair. Earlier free-oracle equality claims are superseded; this table is a review, not a kernel check. |
| M0 proof inventory | 146 named sorry bodies; all have Proof sketches. Targets are definitions with proved readers; their truth is not asserted. |
| Elaboration, all new modules and affected reruns | Lead-reported passing runs exist; bind final counts and source hashes to the final candidate from actual logs. No independent run was made here. |
| decls2 / typed StmtDump / clashes | Lead-owned; do not copy the lexical 674 count into these fields. Refresh from their actual outputs. |
| Canonical seals / paired controls / explicit-unfold scan | Lead-owned and pending report integration; do not mark complete based on source inspection. |
| Axiom census / headline prints / sorryAx graph | Lead-owned; M0 holes can propagate to stored definitions. Final graph must be empty of sorryAx after all Phase A proofs are filled. |
| Duplication scratch probes | Text searches recorded in owner notes; exact?/apply? are lead-only and were not run by this subagent. |
| Full lint / campaign diff / sk15 | Use lead's actual final-candidate logs. Historical staged-source lint results do not bind the final candidate. |
| Replay / bundle / source manifest / delivery ZIP | Lead-owned delivery checks; not run by this reviewer. |

The helper plan remains Phase A. No word-RAM program, RAM bridge, fair-coin product
sampler, efficiency proof of a target, or unconditional efficient primitive belongs
in this delivery.

The three derived Samplers correspondence equations `jlsSPRG_raw_idSamp`,
`jlsSPRG_raw_sdSamp`, and `jlsSPRG_raw_encPP` now have proved bodies in this candidate.
They have been removed from the hole appendix. The lead reports the affected prefix
checks passed; bind the actual logs and source hashes in the validation evidence.

Lead-reported final-candidate gate counts: decls2 ADDED 670, CHANGED 0, REMOVED 0.
The separate source-header count also has 670 named headers, plus four anonymous
instance positions. Equality of these named counts is not an independent elaboration
check; attach the lead's actual decls2 and typed StmtDump artifacts.

Pre-M0 source refinements since b80bfb901: the precise Floor.Semifield import in
Stretch; Samplers transport proofs now read Raw Fintype instance equations; twelve
inference-only binder warnings were addressed with _kappa binders; SP-W2 renames
and changes only two auxiliary hybrid correspondence statements to acceptance
equalities. Headline theorems, algorithms, targets, and assumptions are unchanged.
The declaration totals are still 670 ADDED / 0 CHANGED / 0 REMOVED relative to the
pinned Lean base, as reported by the lead; the two auxiliary replacements occurred
before any M0 freeze.
