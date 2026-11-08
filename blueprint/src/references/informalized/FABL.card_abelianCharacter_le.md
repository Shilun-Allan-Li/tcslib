<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter08/AbelianGroups.lean :: FABL.card_abelianCharacter_le -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Upper bound on character count

**Claim.** The characters of a finite abelian group $G$ number at most $|G|$.

**Proof.** The general cardinality bound for additive characters states that the number of characters from a finite group into the complex numbers is at most the group's cardinality. Apply it to $G$ and $\mathbb C$ (`AddChar.card_addChar_le G ℂ`).
