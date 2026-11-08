<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter08/ProductFourierBases.lean :: FABL.threePointBothCIndicator_fourier_expansion -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Two-Coordinate Indicator Expansion

**Claim.** At every pair of points, the two-coordinate indicator equals its Fourier expansion with coefficients given by the products of the one-coordinate indicator coefficients.

**Proof.** The product Fourier basis expansion theorem ( `FiniteFourierBasis.fourier_expansion`) expresses the function at each point as the sum of its Fourier coefficients times the corresponding product-basis functions. Substitute the coefficient table ( `threePointBothCIndicator_fourierCoeff_table`), which gives each coefficient as the product of the two one-coordinate coefficients. This yields the displayed expansion.

**Key facts.** `FABL.FiniteFourierBasis.fourier_expansion`, `FABL.threePointBothCIndicator_fourierCoeff_table`.
