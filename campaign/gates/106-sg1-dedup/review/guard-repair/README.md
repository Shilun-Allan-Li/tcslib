# Gate 106 F1: guard-helper mechanical repair proposal

**The bounded replacement probe passes.** No production source or Git state was
changed. Root can apply the two body-only proposals, then run the actual module
checks and current merged-tree replay before issuing follow-up audit evidence.

Files:

- `SAT.replacement-declaration.lean.txt`, `Hardness.replacement-declaration.lean.txt`:
  existing complete private headers with replacement bodies.
- `SAT.diff.txt`, `Hardness.diff.txt`: body-only unified diff proposals.
- `SAT.proposed.lean.txt`, `Hardness.proposed.lean.txt`: full proposed source copies;
  every surrounding byte and import is unchanged.
- `receipt.json`: original/full proposed source SHA-256 preconditions, header and
  declaration hashes, actual probe/log hashes, exits/times and control multiplicity.

The two original formulas are identical modulo private declaration name. Each
replacement constructs a first segment from `c` to `d` using supplied endpoint `he`,
and a second from `d` to `tm.runFrom d b` using its reflexive endpoint. Both use the
forbidden set `{some anchor}` and trivial head relation `fun _ => True`; their
strict cuts are exactly the supplied `ha` and `hb`, read through singleton membership.
The proof composes with **`Turing.Segment.trans`**, then projects the composed cut
through **`Turing.segment_iff`**. It contains no time split, subtraction, run-add
argument, induction or replacement concatenation implementation.

`probes/GuardSegmentSealed.lean.txt` imports only the public `Contract.Basic` home,
uses the exact common formula, and seals `Turing.Segment` before the proof. It ran
through `leanelab.sh` against the complete **oleans-msg3** tree, exit **0**, zero
errors/warnings, with only **`propext, Quot.sound`**. No new import is proposed in
SAT/Hardness; their existing current SG-1 contexts reach Basic transitively.

The two Segment delta controls (pointwise iff and parameter-abstracted equality)
pass unsealed, exit 0. Their identical sealed counterparts fail, exit 1, at exactly
lines **12 and 19**, one error each and no extras. This confirms effective sealing;
no failed check is used as positive proof evidence.

All three checks ran sequentially through the authorized wrapper and shared slot
locks. No cache, screen, production-source edit, Git operation, commit or push was
performed. Every actual Lean input used a temporary path; archived source copies
here use `.lean.txt`. There are no new final-patch public or private declarations,
statement/visibility changes, or design/API decisions. The original helper docstrings
and all other source text are preserved.

The successful check is a generic proof/type and Segment-boundary check. It does
not claim a full SAT/Hardness elaboration, production proof seal, current-campaign
replay, external follow-up gate closure or merge clearance. Those remain with root.
