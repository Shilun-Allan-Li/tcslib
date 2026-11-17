<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter06/Constructions/SmallBiasVariants.lean :: FABL.vectorWalshCharacter_fieldPairingGenerator -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Walsh Characters and Field Pairings

**Claim.** The Walsh character of the field pairing generator indexed by $\gamma$ equals the Walsh character indexed by the coordinate vector of the field pairing coefficient, evaluated at the coordinate vector of $s$.

**Proof.** Express each side as the binary sign of a dot product using the character evaluation formula (`FABL.vectorWalshCharacter_apply`). The dot product of $\gamma$ with the field pairing generator equals the dot product of the encoded field pairing coefficient with the encoding of $s$ (`FABL.f₂DotProduct_fieldPairingGenerator`). Applying the same binary sign to these equal dot products proves the identity.

**Key facts.** `FABL.vectorWalshCharacter_apply`, `FABL.f₂DotProduct_fieldPairingGenerator`.
