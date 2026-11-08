<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter07/CNFReductions.lean :: FABL.literalHolds_negate_iff_not -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Negating a Literal

**Claim.** The negated literal holds under an assignment if and only if the original literal does not hold.

**Proof.** At the literal's coordinate, both the assigned sign and the required sign are either $1$ or $-1$. Check these four possibilities. Negating the required sign makes it equal to the assigned sign precisely when the original required sign was different from the assigned sign. Since there are only two possible signs, that is exactly when the original literal fails.
