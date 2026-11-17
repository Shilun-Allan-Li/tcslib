<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/ClassPSPACE/TQBFHardParams.lean :: Complexity.TQBFHard.map_quantBit_levelQuants -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Quantifier bits match level bits

**Claim.** Replacing each existential quantifier in the level quantifier list by true and each universal quantifier by false gives exactly the level bit list.

**Proof.** Induct on the depth. At depth zero both lists are empty. At successor depth, the quantifier list starts with $w$ existential quantifiers, then two blocks of $w$ universal quantifiers, followed by the previous-depth list. Mapping quantifiers to bits turns this prefix into $w$ true bits followed by $2w$ false bits; by induction the remaining bits are the previous level bit list. The definition of the level bit list makes it the concatenation of this prefix with the previous-depth list of bits.
