<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter04/Parity.lean :: FABL.parityBlockCoordinate_injective -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Injectivity of the parity block coordinate map

**Claim.** For the valid block slots $j$ with $gr+j<n$, the map sending $j$ to the coordinate $gr+j$ is injective.

**Proof.** Take two valid slots whose image coordinates are equal. Equality of the finite coordinates gives equality of their underlying natural-number values, so $gr+i=gr+j$. Cancelling the common summand $gr$ yields $i=j$, hence the two subtype slots are equal. Thus the map is injective.
