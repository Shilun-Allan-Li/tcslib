<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter07/AlgebraicPCPP.lean :: FABL.isAffineFrequencyCharacter_iff_twist_isPerpendicularCharacter -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Affine Characters and Perpendicular Twists

**Claim.** A sign-valued function is a character indexed by some vector in $a+V$ if and only if twisting it by the character indexed by $a$ gives a character indexed by a vector in $(V^\perp)^\perp$.

**Proof.** For the forward implication, write $f$ as the character indexed by $\gamma\in a+V$. Membership in the affine subspace means $\gamma+a\in V$ (`mem_binaryAffineSubspace_iff_add_mem`). Twisting the character indexed by $\gamma$ by the one indexed by $a$ gives the character indexed by $\gamma+a$ (`signTwist_f₂SignCharacter`). Since $V=(V^\perp)^\perp$ (`perpendicularSubspace_perpendicularSubspace`), this index lies in the required perpendicular subspace, proving the twisted function is a perpendicular character.

Conversely, suppose the twist of $f$ by the character indexed by $a$ is the character indexed by some $\delta\in(V^\perp)^\perp$. The double-perpendicular identity gives $\delta\in V$. Then $\delta+a$ belongs to $a+V$, by the affine-subspace membership criterion and the fact that adding a vector to itself is zero over $\mathbb F_2$. The twist operation is an involution (`signTwist_involutive`); applying it again and using the character-twist identity shows that $f$ is the character indexed by $\delta+a$. This establishes the reverse implication.

**Key facts.** `FABL.mem_binaryAffineSubspace_iff_add_mem`, `FABL.signTwist_f₂SignCharacter`, `FABL.perpendicularSubspace_perpendicularSubspace`, `FABL.signTwist_involutive`.
