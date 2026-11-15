# Final eleven helper modules: read-only documentation audit

Auditor: seq-zk-a. Scope is exactly the eleven actual root sources named by
`evidence/final-helper-order-01.txt`, including ComputationalTransfer. Source SHA256 values
and complete declaration/doc inventories are in final11-source-audit-inventory.json.
This audit performed no Lean command, source edit, mathematical review or API review.
All evidence files here are newly created outside the historical frozen CP3 receipts.

## Concrete finding to fix before final proof commit

`TCSlib/Cryptography/Composability/SequentialZK/HybridRecursion.lean:46`,
`hybrid_recursion_gap_le`: the32line proof body has a clear English sketch but zero inline
major-stage comments. It has distinct expectation/reindexing, adjacent-gap averaging and
telescoping stages. Brief §Docstrings and sketches and policy §3 require stage comments
for long proofs. Add2–3comments tying those existing stages to the sketch; no mathematical
change is needed. The lead and seq-zk-c were notified immediately. This finding refers to
the audited bytes; any subsequent owner comment-only correction needs its own new source
hash/check record and does not invalidate the original finding.

No other concrete documentation, reader, sketch, width, file-size, reference-section or
new-global-simp violation was found in these eleven modules.

## Mechanical inventory, manually checked

The scanner found44named declarations, six public definitions/abbreviations and14proof
bodies of at least15textual lines. Every named public declaration has an immediately
preceding docstring. All six definition/abbreviation readers exist literally in the same
module, as listed below. All14≥15line proof candidates have a **Proof sketch.** paragraph.
Every file has a References section, is at most1000lines, and has maximum line width≤100.
No new global simp attribute appears. Anonymous typeclass instances are exempt from the
public-docstring requirement; the explicit Nonempty metadata instance is documented anyway.

| Source and line | New definition/abbreviation | Exact reader |
|---|---|---|
| `TCSlib/Cryptography/Composability/SequentialZK/ComputationalReduction.lean:46` | `reductionData` | `reductionData_eq` |
| `TCSlib/Cryptography/Composability/SequentialZK/ComputationalReduction.lean:98` | `phaseContinuation` | `phaseContinuation_eq` |
| `TCSlib/Cryptography/Composability/SequentialZK/BoundedMetadata.lean:45` | `PhaseMetadata` | `PhaseMetadata_eq` |
| `TCSlib/Cryptography/Composability/SequentialZK/BoundedMetadata.lean:67` | `toData` | `toData_eq` |
| `TCSlib/Cryptography/Composability/SequentialZK/ContinuationProbability.lean:87` | `continuationProb` | `continuationProb_eq` |
| `TCSlib/Cryptography/Composability/SequentialZK/ContinuationProbability.lean:309` | `phaseGap` | `phaseGap_eq` |

Manual review confirmed that the six reader statements expose full equations/types, rather
than only isolated consequences. In particular PhaseMetadata's abbreviation has its type
equality, toData has the complete packed-word equation, the continuation data and machine
continuation have complete equations, and continuationProb/phaseGap expose their entire
acceptance/advantage experiments. There are no new predicates without iff readers and no
new structure-valued definition requiring additional simps projection equations in this set.

The public docstrings state the represented value, equation, inequality or sampler operation
with the relevant assumptions. Source-derived constructions/results have PS10/Gol01 tags;
pure coin/probability/encoding glue has explicit formulas and does not require a separate
textbook counterpart. The English sketches match the visible major proof stages.

## Long-proof stage comments

| Source and declaration | Body lines | Inline stage-comment count |
|---|---:|---:|
| `TCSlib/Cryptography/Composability/SequentialZK/ComputationalReduction.lean:132` `phaseContinuation_poly` | 33 | 2 |
| `TCSlib/Cryptography/Composability/SequentialZK/ComputationalReduction.lean:185` `exists_continuationSampler` | 42 | 2 |
| `TCSlib/Cryptography/Composability/SequentialZK/HybridRecursion.lean:46` `hybrid_recursion_gap_le` | 32 | 0 |
| `TCSlib/Cryptography/Composability/SequentialZK/RealPrefixBounds.lean:54` `realPrefix_bounds` | 38 | 3 |
| `TCSlib/Cryptography/Composability/SequentialZK/ContinuationProbability.lean:114` `continuationProb_bellman` | 32 | 2 |
| `TCSlib/Cryptography/Composability/SequentialZK/ContinuationProbability.lean:169` `continuationProb_real` | 78 | 3 |
| `TCSlib/Cryptography/Composability/SequentialZK/ReductionAdvantage.lean:59` `distAdv_phaseReduction` | 32 | 2 |
| `TCSlib/Cryptography/Composability/SequentialZK/ComputationalHybrid.lean:48` `prefix_distAdv_le` | 54 | 3 |
| `TCSlib/Cryptography/Composability/SequentialZK/ComputationalPhaseBound.lean:63` `exists_negligible_phase_bound` | 109 | 7 |
| `TCSlib/Cryptography/Composability/SequentialZK/ComputationalTransfer.lean:55` `zk_of_padded_spec` | 40 | 3 |

Manual inspection confirmed the comments in the other long proofs identify their major
construction, reindexing, fixed-point, selection, or endpoint stages. The shorter15–24line
proofs also have sketches; they use short direct compositions or a single local comparison
and were not classified as a missing long-proof stage-comment requirement.

## Heuristics versus manual conclusions

final11-source-audit.py is a static Python inventory, not a Lean parser. It recognizes
column-zero declaration starts, nearest declaration docstrings, literal reader names and
`:= by` proof bodies, ending the latter at the next declaration/docstring/namespace. Thus
the reported textual line lengths and comment counts are triage heuristics. The ≥15line
sketch threshold is the brief's explicit rule. The ≥25line long-proof filter is an audit
convention, not a numerical threshold stated by policy; the concrete32line HybridRecursion
finding was manually confirmed to contain several distinct major stages and no comments.

Manual review covered all six public definitions/readers, all44named public docstrings,
all14sketch candidates and all long-proof comment candidates in the source order. This
check does not replace the lead's native compilation, standard-axiom census, full strict/coe
Rule10 seals or final style-lint comparison. The prior CP3/main/Sims/Prefix comment findings
are outside this eleven-module scope and were not reopened.

Retained files: final11-source-audit.py; final11-source-audit-inventory.json;
final11-source-audit-inventory.log; final11-source-audit-inventory.stderr;
final11-source-audit-docstrings.log; this audit report. All are separate from the historical
frozen receipts and contain no proof-source modification.
