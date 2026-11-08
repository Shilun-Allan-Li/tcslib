<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter07/AlgebraicPCPP.lean :: FABL.pcppBoolCubeEquiv_innerProductFlipNeighbor -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Encoding a Flipped Binary Neighbor

**Claim.** For positive $m$, encoding the Boolean vector obtained by the inner-product flip-neighbor operation gives the binary vector obtained by applying the corresponding operation over $\mathbb F_2$ to the encoding of the original vector.

**Proof.** By definition, the Boolean flip-neighbor is obtained by applying the binary operation to the encoded vector and then applying the inverse cube equivalence. Encoding this result cancels that inverse equivalence, leaving precisely the binary operation applied to the original encoding.
