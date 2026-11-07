# Fresh current-source screen classification

Same nine-file population in both runs; exact source hashes, temporary tree arguments, script hashes, raw stdout/stderr and exit receipts are archived. Both screens were executed for this round under one continuous shared screen lock, serially, and the lock was released. Parsing independently verifies every edge count and reproduced-character sum.

| Comparison | Eligible declarations | Directed pairs | Reproduced characters |
| --- | ---: | ---: | ---: |
| Current base | 1,559 | 1,583 | 492,990 |
| Current head | 1,561 | 1,583 | 494,807 |

Current base → head has one new edge, one gone edge, 1,582 retained edges and eleven retained edges whose metrics change. These are candidate measurements, not debt-member counts.

- **Gone:** `Basic.lean::Turing.Segment.trans` reproducing `Tautology.lean::tautDual_segment_add`, 91/168 (54%). The private concatenation proof is deleted and its consumers use the published API.
- **New:** `SingleTape.lean::dg_turn_with_growth` reproducing `dg_end_with_growth`, 784/1,564 (50%). The shared transition/frame skeleton predates the PR; both use the already audited public Segment bridge/composition. Their distinct states, end configurations and bounds remain. This is a non-identical in-file near-match under the standing accounting convention, not a new private composition implementation or newly accepted family. The reciprocal edge was already present and changes 736/1,283 → 784/1,331.
- **Four CounterLoop metric changes:** the two done/escape witness directions and the two RoundContract trajectory directions gain the already audited `segment_iff` constructor/projection readings. Statements are frozen, and their exact source blobs match the previously executed seals.
- **Four Tautology metric changes:** reciprocal scan/copy and valid/invalid edges change when the public Segment composition replaces the old private helper. Complete source identity with the audited head establishes that these are the earlier classified transformations, not additional round-two implementations.
- **Two guard metric changes:** the reciprocal SAT/Hardness guard edges remain 100%, now 525/525 rather than 127/127. Both retain exact generic headers and reuse `segment_iff`/`Segment.trans` instead of their old time split. Each exact original-import-context body passes the new seal. These are existing private compatibility adapters to a published theorem, not a retained derivation of cut composition. The 398-character rise in each direction is still reported as text overlap, not discarded.

The immutable audited head and current head have **identical directed edge sets**. Only those last two guard metrics change, adding 796 characters to the former 494,011-character total. Current NatBits-era source has two fewer eligible bodies than the historical population but no additional changed edge: the historical base and current base edge sets/metrics are identical. These current comparisons do not overwrite the historical screen.

All **86** directed SAT/Hardness candidates remain. Their current edge metrics and dispositions are in `../current-sat-hardness-candidates.json`; all supplied historical edges have a current counterpart. The five explicitly acknowledged adapter kinds still have 22 distinct source-inclusive members per file (44 total), not 86 members. The separately acknowledged dispatcher contributes six non-abbreviations plus its state alias per file; concrete HostNext tables are client data. The old live-prefix watch and wider RO-1/statement-specific candidates remain separate. The known named lower bounds are SAT **34/270**, Hardness **32/544** after F1 repair, including notation; neither is an exhaustive cleared census or a new one-fifth crossing.

Primitives/Catalog SafeSegment siblings and their broader pre-existing acknowledged material are unchanged by this PR and retain their recorded independent families. The Segment source is not double-counted. SG-1 and the mechanical F1 re-derivation retirements occur on merge, not on this evidence run. The screen neither grants a new debt acknowledgment nor closes the gate.
