Replaces the three private Segment-specialization composition proofs with the published
Segment API, retaining their exact statements and consumer behavior. The same-PR mechanical
review also repoints the two older SAT/Hardness cut guards to segment_iff/Segment.trans.
The current Lean diff is five files; the identical Frag repair is already common through #222.
Only the two previously approved Basic imports are added; existing public statements and
machine definitions remain fixed.

Gate106 round1 returned HOLD0/2/1/9. Both cut re-derivations are repaired; Seyoon explicitly
accepted the five generic adapter kinds plus the separate finite-family dispatcher kind,
with companion proofs, for maintainer cleanup in the next12.2c SAT/Hardness consolidation
after activeMIG1 and before further fills in those files. The SingleTape accounting minor is
corrected to six consumer declarations/twelve calls; original packet remains immutable.

Validation: current329-module merged-tree replay passes, zero failures/static mismatches.
Full nine-file source/compiler freeze, actual guard axioms and both-definition seals with
four paired controls pass. Fresh complete screen has no new cross-file edge; all retained
candidate/debt lower-bound and watch distinctions are documented. Round2 Codex packet is
published and ready for user dispatch; exact pins/evidence are under campaign/gates/106-sg1-dedup/.

**Not yet clear to merge.** Gate106 follow-up must close; Seyoon merges.
