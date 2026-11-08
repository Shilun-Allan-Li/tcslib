<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter08/ProductFourierBases.lean :: FABL.threePointBothCIndicator_fourierCoeff_table -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Two-Coordinate Fourier Coefficient Table

**Claim.** For each pair of indices $(a_0,a_1)$, the Fourier coefficient of the two-coordinate indicator is the product of the one-coordinate coefficients at those indices.

**Proof.** Apply the coefficient formula for the two-coordinate indicator ( `threePointBothCIndicator_fourierCoeff`): its coefficient is the product over the two coordinates of the corresponding one-coordinate coefficients. Expanding this two-term product gives $\widehat g(a_0)\widehat g(a_1)$, as claimed.

**Key facts.** `FABL.threePointBothCIndicator_fourierCoeff`.
