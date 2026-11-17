<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter06/Constructions/SmallBiasGenerator.lean :: FABL.f₂DotProduct_smallBiasGenerator -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Pairing Identity for the Small-Bias Generator

**Claim.** The dot product of γ with the small-bias generator at r,s equals the dot product of the encoding of the polynomial with coefficients γ evaluated at r and the encoding of s.

**Proof.** First evaluate the polynomial using the identity `FABL.smallBiasPolynomial_eval`: its value is the sum of the terms γᵢ times r to the power i+1. Linearity of the encoding carries this weighted sum to the corresponding sum of encoded powers. Substitute that expression into the right-hand dot product and expand both dot products in basis coordinates. Distribute the outer coefficients, interchange the finite sums over generator indices and basis coordinates, and factor out each coordinate of the encoding of s. The resulting sum is the dot product of γ with the generator vector.

**Key facts.** `FABL.smallBiasPolynomial_eval`.
