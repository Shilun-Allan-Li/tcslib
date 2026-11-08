<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter06/Constructions/ExecutableVandermonde.lean :: FABL.executableVandermondeFieldPoint_power -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Powers of the Field Points

**Claim.** For every allowed exponent index $q$ and point index $j$, encoding the binary modular power of the point with exponent $q+1$ and applying the field isomorphism gives the $(q+1)$st power of the corresponding field point.

**Proof.** The field degree is positive. The power-encoding identity (`binaryAdjoinRootEncode_binaryPowMod`) identifies the encoded modular power with the $(q+1)$st power of the encoded point in the adjoining-root field. Applying the algebra isomorphism to this equality preserves powers, and the image of the encoded point is exactly the defined field point. This gives the stated identity.

**Key facts.** `FABL.ExecutableVandermondeInput.fieldDegree_pos`, `FABL.binaryAdjoinRootEncode_binaryPowMod`.
