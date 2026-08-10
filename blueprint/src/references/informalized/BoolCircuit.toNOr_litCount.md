<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/Switching/Circuit.lean :: toNOr_litCount -->
<!-- origin: no source citation; informalized directly from the Lean proof -->

# OR-rooted normalization preserves the literal count

**Claim.** For every circuit `c : Circuit n`,
`(c.toNOr).litCount = c.litCount`: OR-rooted normalization changes only gate
structure, not the number of literal occurrences.

**Proof.** Immediate from the combined statement —
`(toNAnd_toNOr_litCount c).2`. A projection wrapper only.
