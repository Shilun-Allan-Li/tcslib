<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter06/F₂Polynomials/Examples.lean :: FABL.f₂DotProduct_f₂CubeOfFinset -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Pairing with a Set Indicator

**Claim.** The dot product of x with the indicator vector of S equals the sum of the coordinates of x indexed by S.

**Proof.** Expand the dot product as a sum over all coordinates. At each coordinate the indicator is 1 when the coordinate belongs to S and 0 otherwise, so the summand is xᵢ on S and zero outside S. Removing the zero terms leaves precisely the sum of x over S. The coordinate description of the indicator is supplied by `FABL.f₂CubeOfFinset_apply`.

**Key facts.** `FABL.f₂CubeOfFinset_apply`.
