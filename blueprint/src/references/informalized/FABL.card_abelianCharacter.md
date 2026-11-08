<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter08/AbelianGroups.lean :: FABL.card_abelianCharacter -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Number of abelian characters

**Claim.** For a finite abelian group $G$, the number of complex-valued additive characters of $G$ equals $|G|$.

**Proof.** Apply the finite-character counting theorem for additive characters: the cardinality of the type of characters from a finite additive group into the complex numbers equals the cardinality of the group (`AddChar.card_eq`).
