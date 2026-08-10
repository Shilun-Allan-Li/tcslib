<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/Switching/Circuit.lean :: toNAnd_litCount -->
<!-- origin: no source citation; informalized directly from the Lean proof -->

# AND-rooted normalization preserves the literal count

**Claim.** For every circuit `c : Circuit n`,
`(c.toNAnd).litCount = c.litCount`: the number of literal occurrences is exactly
preserved by AND-rooted normalization (unlike `size`, which can double).

**Proof.** Immediate from the combined statement —
`(toNAnd_toNOr_litCount c).1`. A projection wrapper only.
