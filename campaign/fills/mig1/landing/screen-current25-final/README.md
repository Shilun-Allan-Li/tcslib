# Final 25-file source screen

**Not yet clear to merge.** This bounded screen is linked byte-for-byte to
PR #233's pushed head `b1f553b315f31b949076e91119473ce4070e7d53`.
The full commit and all 25 full Git blob objects were checked read-only;
all captured bytes and the local origin tracking ref match. Root's push
receipt is retained. This child made no live remote/network query.

The one fresh final head screen passed in **539.41 seconds**, using the
same unmodified v3 script, all 25 complete files, Python isolated mode,
niceness 10 and the shared screen lock. The baseline and phase2 outputs
were reused after checking their source/tool hashes and the immutable
136-entry phase2 manifest. Neither earlier tree was retiled.

| Metric | API1160 baseline | Phase2 | Final |
| --- | ---: | ---: | ---: |
| Screened declarations | 1,499 | 1,234 | 1,234 |
| Cross-file proof candidates | 782 | 120 | 122 |
| Cross-file term candidates | 150 | 16 | 16 |
| In-file proof candidates | 666 | 411 | 410 |
| In-file term candidates | 98 | 74 | 74 |
| All directed candidates | 1,696 | 621 | 622 |
| Sum of reproduced characters | 656,226 | 194,045 | 195,289 |

Against baseline: **54 new / 1,128 gone**, with 29 surviving pairs changing
metrics. Against phase2: **two new / one gone**, with two surviving pairs
changing metrics. Both complete deltas, every candidate/index, all 75
inert source inputs, commands, tool hashes and raw logs are retained
without caps. Counts and character sums describe directed textual
matches, not independent semantic copies or duplication-ledger rates.

Only `Primitives.fwdMapVirtual_run` changed normalized extracted body;
all 1,234 labels and kinds remain the same. Source QA verifies the exact
three tagged drivers—this private lemma, `bufferedSecondCfg_run` and
`vhostEmitTM_runFrom`—all use `Set.MapsTo.iterate` and
`add_right_iterate`, with no induction. The private header remains literal.

The two new phase2-relative edges are the private driver reproducing
429/640 characters of the virtual-host reader and 426/707 of the buffered
reader. Reverse edges already existed and now have larger weights. The
private-to-setup-run edge disappears. This explains the net increase of
one candidate and 1,244 characters after moving all three instances onto
the existing generic iterator. The remaining text is material concrete
predicate, initial-tag and step/witness-premise scaffolding; it is not
hidden or declared approved. All six directed matches among these three
instances, including the two older public/public directions, are retained
in `all-six-tagged-instance-candidates.json` for external assessment of
the interface reuse. No broad debt exemption is inferred.

[semantic-review.md](semantic-review.md) assigns every baseline-new edge
and both phase2-new edges exactly once in 18 source-read groups. Unchanged
phase2 classifications remain explicitly linked. The source check also
verifies single helper calls in the terminal, bank-frame, buffer-rewind
and canonical-endpoint families and absence of the retired selector
helpers. No new proof implementation was performed in this review.

Retained watches remain visible: the fuel/orbit/round-assembly scaffold
newly exposed by the emitting proof's shorter denominator; statement/type
tails included by v3 in let-bound private headers; thin call/field/tape
case scaffolding; and distinct frozen executable-table data. The unchanged
first-entry twin, both zero-space rows and the redirect home HOLD remain
pending. This report approves none of those decisions or retained debt.

`capture.json` pins all 25 actual files: 12 differ from API1160; only
Primitives differs from phase2, at SHA256
`72226a291b0c7e9189883a0ebd75a88ca49bb1f19d0487e54316e542b847ee71`.
The other 24 files match phase2 byte for byte. `pushed-head-linkage.json` verifies
all 25 committed blobs against that capture; `verification.json` checks
the final live source and complete raw evidence. The original baseline's
commit/blob verification receipt is reused explicitly.

Only text-screen and read-only source/evidence/Git-object checks ran here:
no Lean, source edit, Git mutation, cache or snapshot operation. The shared
lock was released normally. `SHA256SUMS` covers this frozen folder except
itself, and the prior phase2 folder remains untouched. This is not a
whole-tree freeze, merged-tree replay, rule-10 seal, complete semantic
duplication audit, hold disposition or gate closure; root's final native,
metadata, source QA, replay and external gate evidence remain separate.
