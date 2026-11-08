Removes the three private Segment concatenation proofs in Tautology, CounterLoop and SingleTape,
replacing them with equation-based bridges and the public Segment API. Older zero/one/mono
helpers and four CounterLoop witness/trajectory reads use the same equations. The original shared Frag
cell-step repair is already common through merged #222; the current Lean diff has three files,
with all four originally audited blobs unchanged. The blueprint follows the deletion.

No public statement, visibility or relative declaration order changes. Source census 287 → 287;
unfiltered non-private compiled census 293 → 293, with no name/kind/module-owner changes.

Validation: fresh post-NatBits 329-module merged-tree replay on `oleans-msg3`,
0 failures/static mismatches (67 inherited admissions; #229 remains separate); all six
changed public bodies use only standard axioms. Whole-file Segment seals in all three consumers
and paired controls pass; Frag cell-step seal passes. Full nine-file screen, freeze, lint and
blueprint checks are retained under `campaign/gates/106-sg1-dedup/evidence/current/`.

**Not yet clear to merge:** external Codex gate 106 remains open. Seyoon merges after it closes.
