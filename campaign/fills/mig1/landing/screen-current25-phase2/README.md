# Frozen phase2: 25-file head screen

**Not yet clear to merge.** This source generation is now linked to the
pushed PR #233 checkpoint `429bdd596adc15f229a8a03993967e5941cc2442`.
It contains the four adopted factoring families and the two public tagged-run
repoints. Its captured source is retained exactly. A standalone pushed
commit and all 25 full blob objects were checked read-only; all 25 source bytes
match, and the local origin tracking ref matches the supplied pushed head.
Root's push receipt is retained; this child made no live network query.
Root plans a further private tagged-run body repoint and a separate final
head screen. That later edit is outside this
generation and does not alter these raw inputs/results.

One fresh head screen passed, using the same unmodified v3 script, all 25
full files, isolated Python, niceness 10 and the shared screen lock. It took
534.35 seconds; the lock was acquired/released normally, with no stale
reclamation. The exact previously executed baseline and previous-head
outputs were reused after verifying the first review's 120-entry manifest;
neither was retiled.

| Metric | API1160 baseline | Previous head | Phase2 head |
| --- | ---: | ---: | ---: |
| Screened declarations | 1,499 | 1,232 | 1,234 |
| Directed proof candidates, cross-file | 782 | 122 | 120 |
| Directed term candidates, cross-file | 150 | 16 | 16 |
| Directed proof candidates, in-file | 666 | 416 | 411 |
| Directed term candidates, in-file | 98 | 74 | 74 |
| All directed candidates | 1,696 | 628 | 621 |
| Sum of reproduced characters | 656,226 | 201,653 | 194,045 |

Against baseline: **53 new / 1,128 gone**, with 29 surviving pairs changing
metrics. Against previous head: **3 new / 10 gone**, with 10 surviving pairs
changing metrics. Both complete pairdiffs, every candidate and source
index, all 75 inert source inputs, commands, tool hashes and raw logs are
retained without caps. Directed counts/character sums are textual
heuristics, not independent semantic-copy or ledger percentages.

[semantic-review.md](semantic-review.md) assigns all 53 baseline-relative
and all 3 previous-relative new edge exactly once, in 18 source-read groups.
All 15 baseline-relative new cross-file edges belong to the prior reviewed
families; there is no new cross-file family versus 628. The three newly
visible in-file edges are:

- `bank_step`→`bank_initial`,336/450, and `bank_embed`→`bank_initial`,294/450:
  unchanged client or provider material overlaps the shortened initial
  wrapper's **let-frame type tail** and specialization call. Its actual
  proof calls the shared bank helper once.
- `loopHost_contracts`→`emitLoopTM_computes`,1,166/2,057: a retained common
  fuel/orbit/round-assembly scaffold becomes threshold-visible after the
  emitting proof's terminal suffix shrinks. The target is unchanged; the
  exact emitting suffix diff is retained. This is disclosed as a residual
  scaffold watch, not new copied text introduced by phase2 or an inferred
  debt approval.

`targeted-reuse.json` independently checks source adoption: all 3 terminal
consumers call `loop_computes_of_startup`, both bank consumers call
`emCall_bank_embed`, both buffer rewind consumers call `fwdMap_back`, and
both endpoints call `catalog_ofWords_with_tapes`, once each. The now-unused
pair/triple selector lemmas are absent. Old high-scoring terminal/bank or
endpoint pairs can still score on call arguments, statements and distinct
per-cell glue; no claim of zero surviving textual similarity is made.

Both public tagged-run bodies use `Set.MapsTo.iterate` with
`add_right_iterate`, and contain no induction. The private
`fwdMapVirtual_run` is unchanged here; the separate next-generation repair
must not be credited to this screen. The first-entry twin, two zero-space
HOLD rows and redirect home HOLD remain unchanged and pending. Frozen
runtime tables are separate term/data matches; no new API, debt or table
exception is approved by this review.

`capture.json` pins the full 25 actual source blobs:12 differ from API1160,
six from the previous screened bytes. Every adopted hash matches root's
receipt. The reused pre-comment previous screen is linked through its
preserved post-comment parser-equivalence receipt to all 25 hashes of the
root-attested passed `0d6b6f842a48be813dcde7fdfd2a1a161fab2383`
generation; no new Git/Lean claim is made. The final live check records
that all 25actual files still matched this capture before root's next edit.

Only the fresh text screen and read-only source/evidence checks ran here:
no Lean, source edit, Git mutation, cache/snapshot operation or additional
tiling. `link_pushed_head.py` performed only the read-only commit/blob and
local tracking-ref checks above. `verification.json` and `SHA256SUMS` cover the exact
bounded evidence; the old 120-entry screen folder remains untouched. This
is not a whole-tree freeze, replay, complete semantic-duplication audit,
hold disposition or gate closure.
