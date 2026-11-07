# Current MIG-1 draft: expanded 25-file copy screen

**Not yet clear to merge.** Both full-population screens passed. This is an
uncommitted draft comparison and bounded source review, with remaining
factoring/disposition and independent API/home holds; it is not a gate or
an acceptance of the partial delivery.

## Executed comparison

The same 25 full files were screened at API prerequisite commit
`1160c18f03fd318f0dec25738790935fa61379d4` and the actual current landing
capture before comment cleanup. The full commit and all 25 baseline blob
objects were verified before writing. All 50 inert `.lean.txt` inputs and
their exact hashes are retained; the actual sources were stable during
capture. Eleven files differ. The population is `population.txt`, with no
file or candidate cap.

| Syntactic screen category | Baseline | Captured draft |
| --- | ---: | ---: |
| Screened declarations | 1,499 | 1,232 |
| Cross-file proof candidates | 782 | 122 |
| Cross-file term candidates | 150 | 16 |
| In-file proof candidates | 666 | 416 |
| In-file term candidates | 98 | 74 |
| All directed candidates | 1,696 | 628 |
| Sum of reproduced characters | 656,226 | 201,653 |

The full delta is **60 new, 1,128 gone**: 17 new cross-file candidates
(13 proof, four term) and 43 new in-file candidates (42 proof, one term).
There are also 27 surviving label-pairs with changed metrics, retained
separately. These are directed textual candidates, not independent
semantic-copy counts or a duplication-ledger percentage.

The unmodified v3 screen ran **serially**, baseline then head, at niceness
10 with Python isolated mode, holding the shared scratch screen lock with
a live PID. Both exited zero; baseline took 841.77 seconds and head
557.48 seconds. `lock-events.jsonl` records both acquisitions/releases;
there was no stale-lock reclamation. Raw outputs, exact commands,
tool-source copies/hashes and unmodified pairdiff output are retained.
No Lean invocation, Git write, source edit, cache or shared-snapshot change
was performed by this review. [method.md](method.md) explains the tool's
thresholds and parser limits.

## Source classification and remaining watches

All **60** new directed edges have exactly one source-read classification
in [semantic-review.md](semantic-review.md), with original scores, source
positions and explicit baseline provenance in
`new-candidate-classifications.json`. This covers every new cross-file
family and groups every new in-file edge; it does not certify the semantic
status of every surviving legacy candidate.

The new cross-file matches comprise four short pair-diagonal witness/spec
packages, two visited-set/card-reader prefixes, seven moved setup/virtual
run-template edges, and four configuration-record data edges. Every moved
setup/virtual origin pair was already reported in the baseline under the
deleted Catalog `a2_map*` names. The two moved record bodies are exact after
the explicit prefix rename. The run-body differences are only explicit
zero-time reader repairs. The shared tagged-run induction remains visible;
root has separately commissioned invariant-route repoints after this
frozen generation. This review applies no such repair.

The substantial **new in-file** operational overlap is
`loopHostTM_decides`/`loopHostTM_finds` (823 shared characters, 93%/87% of
the respective source body), with the emitting proof sharing the startup
composition/time-bound suffix. It was reported to root, who assigned a
separate factoring review. Other important **retained** watches include
the moved `fwdMap_backA`/`fwdMap_backB` mirrored rewind proofs and the
`emCall_bank_initial`/`emCall_bank_final` frame scaffold. Their existing
baseline label/origin relationships are recorded; they are not silently
marked approved or discharged. [residual-watches.md](residual-watches.md)
gives exact metrics and limits.

Several new T2 and Wrappers candidates include theorem-type tails because
v3's depth-zero delimiter treats `let B := ...`/`let V := by ...` in a
type as body text. In particular the actual left/right erase consumer
proofs are only specializations of the one private erase proof. Their
large displayed overlaps do not establish duplicate erase derivations.
The screen was not altered to hide these candidates.

## Named assignment reconciliation

`assignment-reconciliation.json` checks the captured sources directly:

- **T1:** `catalogRewind` is gone. Each of its four callers differs from
  baseline only by the callee substitution to public `timed_rewind`.
- **T2/T2b:** seven private proof helpers serve the named rewind, bank,
  administrative-frame, embedding-field, erase, split-orbit and replay
  families. Every named consumer calls its helper once. This does not
  claim all other parser/frame templates are gone. The generated split
  equations' separate availability/policy review remains separate.
- **T3:** the two bank proofs' six repeated side-proof markers each are
  gone, replaced by eight pair-selector and four triple-selector helper
  calls in total. The two helpers retain a disclosed five-line proof
  template; the bank proofs retain other common frame text.
- **T5:** copy/transfer endpoints share `catalog_buffer_clip`; successful
  and overflow increments share `catalog_increment_framed`. The frozen
  `copyMapTM`, `transferMapTM` and `clearTM` bodies match baseline. Their
  remaining term matches are executable data: copy preserves the source
  on rewind, transfer writes its configured residue. No table-rewrite
  exception or new debt acknowledgment is inferred.
- **T6:** all three extraction-space rows call `pairExtract_space_row`.
- **First-entry:** the Loop/Primitives twin is unchanged, remains an exact
  403/403-character proof-body match both ways, and awaits the separate
  shared-API ruling. It is not removed by a new-pairs-only summary.

The canonical zero-space resource facts and redirect theorem's public-home
exception remain independent holds. Nothing here closes them or approves
retaining further proved duplication.

## Link to post-comment source and evidence limits

After both screens, a separate read-only check captured all 25 final
actual post-comment files. The trusted v3 parser produced the **same
1,602 complete extracted declarations and 1,232 screened declarations**:
names, namespaces, kinds, flags and normalized bodies match; screened
labels/kinds/bodies match exactly. Only offsets/line numbers were ignored.
`comment-linkage/equivalence.json` pins root's cleanup receipt and all final
actual hashes. All actual sources remained stable during that check, and
**zero extra tiling runs** were added. Original raw inputs/hashes remain
the pre-comment capture.

This equivalence links only that proof generation and comment cleanup.
Later proof repairs require a refreshed head screen, source linkage and
appropriate validation; the present raw evidence remains immutable.
Complete raw lists and source snapshots are retained without truncation.
`SHA256SUMS` covers the finalized review folder except itself. No replay,
global semantic-duplication clearance, debt approval or gate closure is
claimed.
