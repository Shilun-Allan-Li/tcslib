<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter07/AlgebraicPCPP.lean :: FABL.completeQuadraticFlipNeighbor_isCompleteQuadraticOne -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Boolean repair satisfies the quadratic condition

**Claim.** For $n\ge2$, converting a Boolean vector to its $mathbb F_2$ encoding, repairing it as prescribed, and converting back yields a Boolean vector whose encoded complete quadratic bit is $1$.

**Proof.** By definition, the Boolean repair converts the input to its coordinatewise $\mathbb F_2$ vector, applies the binary repair, and converts back. Applying the coordinatewise encoding to that converted-back vector recovers the repaired binary vector, since the encoding equivalence and its inverse cancel. The binary repair theorem then gives complete quadratic bit $1$ (`completeQuadraticFlipNeighborBinary_is_one`).

**Key facts.** `FABL.completeQuadraticFlipNeighborBinary_is_one`.
