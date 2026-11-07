# SG-1 final screen and candidate classification

Both runs use the complete nine-file population: four changed files plus Contract/Basic, Primitives, Catalog, SAT and CookLevin/Hardness. The source pins are beside the raw outputs. The final head is the repaired head, not the historical pre-seal head retained in `before-seal-repairs/`.

The screen reports **1,561 → 1,563 eligible declarations, 1,583 → 1,583 directional candidate pairs, 492,990 → 494,011 reproduced normalized characters**. These eligible-body counts differ from the four-file source census, which remains 287 → 287 declarations.

One pair disappears: Basic's `Segment.trans` reproducing the deleted `tautDual_segment_add`, 91/168 characters (54%). One pair appears: SingleTape's `dg_turn_with_growth` reproducing `dg_end_with_growth`, 784/1,564 characters (50%). Their common transition scaffolding predates the PR; both now use the shared Segment composition. This is an in-file near-match, not an exact copy or a new re-derivation of the composition theorem. The ledger's standing in-file convention records it without adding a debt member. No new cross-file pair is reported. The other 1,582 head pairs were present at base.

The source/semantic pass finds and replaces all three known private concatenation helpers via their Segment bridges. It also replaces the older zero/one/monotonicity implementations in the touched specialization files: Tautology's zero/one helpers and SingleTape's one/mono helpers. Four older public CounterLoop reads now use `segment_iff`; the first failed seal is retained with its mechanical resolution.

The retired concatenation names have no head-tree hits. Broader predicate and run-addition searches are candidate enumeration, not an exhaustive theorem. The SafeSegment siblings in Primitives/Catalog and cut-only SAT/Hardness routines were already disclosed separately in the ledger; the PR does not claim to retire them or infer a new acknowledgment. The existing cumulative ledger governs historical debt in these files; a raw candidate-pair count is not a debt-member count. No new file crosses one fifth through this change.
