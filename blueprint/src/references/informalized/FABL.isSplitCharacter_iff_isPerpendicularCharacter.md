<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter07/AlgebraicPCPP.lean :: FABL.isSplitCharacter_iff_isPerpendicularCharacter -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Split and perpendicular characters

**Claim.** A function is a split character for the chosen decomposition exactly when it is a character whose frequency lies in the perpendicular subspace to $H$.

**Proof.** Suppose first that $f$ is a split character, so it is the character associated to some complementary frequency $\gamma$. The lifted frequency belongs to $H^\perp$ by the fact that lifting a complementary frequency produces a perpendicular frequency (`FABL.BinarySubspaceSplit.liftFrequency_mem_perpendicularSubspace`). Moreover, the split character agrees pointwise with the ordinary character of this lifted frequency (`FABL.BinarySubspaceSplit.character_eq_liftFrequency`). Hence $f$ is a perpendicular character. Conversely, suppose $f$ is the character of a frequency $\eta\in H^\perp$. Restricting this frequency to the complementary coordinates gives a frequency whose split character agrees pointwise with the character of $\eta$ (`FABL.BinarySubspaceSplit.character_restrictFrequency`). Therefore $f$ is a split character.

**Key facts.** `FABL.BinarySubspaceSplit.liftFrequency_mem_perpendicularSubspace`, `FABL.BinarySubspaceSplit.character_eq_liftFrequency`, `FABL.BinarySubspaceSplit.character_restrictFrequency`.
