# Private full-target canonOffset reader repair

The exact existing-API patch replaces only the foreign-definition conversion
`change Nat.bit true (codeBitsNat w.length.bits + 1) = _` with
`rw [← codeBitsNat_eq]`, retaining the existing Nat.bit_val repair. Source is
relative to actual PR247 head d725e9fa76c81623e95c350250853bec511ddc3c.
Complete before/proposed owner, exact one-line patch and source freeze are given.
Proposed owner SHA256:
8f1b19cf6893b7129e6d98ced5572633f6ed04a1b2fcd5767d04e136e7cef9c8.

The complete owner passes natively against whole MAC8, source9b5, with original
imports and zero errors/warnings/sorry warnings. A full-owner inventory walks
root and same-owner helper theorem/definition types AND values; imported theorem
proof values remain boundaries. Exact ordinary TCS heads are codeBitsNat and
incFixed, plus focused Mathlib Nat.bit. No default-simp definitions to remove.
The COMPLETE target doc/header/body passes both native and sealed owner probes
under all3 guards, with standard AX [propext, Classical.choice, Quot.sound].
Six final kernel-checked controls pass natively and their exact six identities
fail sealed. The two incFixed controls are its nil/false-cons equations. The
initial generic reflected incFixed controls fail even normally; original sources
and failed logs are preserved and not counted as effective evidence. No unsafe
transparency or reducibility override is used. explicit-argument-review.md lists
every target rewrite/simp/change and the precise scope boundaries.

This is the one complete target seal, not a seal of the entire legacy owner or
earlier same-owner helper proofs. The latter are inspected for footprint but
remain unchanged; imported theorem proof values/Core internals stay boundaries.
No new interface/import/header/definition/name/home or mathematical fill.
No actual source/Git/canonical/snapshot mutation, commit, push, screen, full23
replay, actual new-HEAD ABI, dispatch or gate closure. Root adoption/publication
and matching new-source replay/screen/metadata remain necessary. The old frozen
226-file gate127 packet stays immutable historical evidence for d725 only.
Seven accepted SG1 kinds, FE/FH/BLIVE separation,54 named union and nine inherited
Primitives closures retain their bounds; no global absence/debt retirement.

All Native work used approved leanelab, one helper slot, local3/machine5,
j4/nice10. Exact source .lean.txt, commands, receipts, all failed preparations,
complete canonical CodeParser/Convention/Mathlib source and full manifest follow.
