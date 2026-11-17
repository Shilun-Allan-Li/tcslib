<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter08/AbelianGroups.lean :: FABL.character_eq_zero_or_expect_eq_zero -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Character Expectation Alternative

**Claim.** A character of a finite additive commutative group is either the zero additive character or its uniform expectation over the group is zero.

**Proof.** Split into two cases. If the character is the zero additive character, the first alternative holds. Otherwise it is nonzero, and the character orthogonality theorem for a finite group says that the uniform average of a nontrivial character vanishes. This gives the second alternative.
