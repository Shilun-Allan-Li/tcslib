<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter05/FKNOptimality.lean :: FABL.fourierCoeff_fknOptimalityFunction_succ -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Shifted Fourier Coefficient Identity

**Claim.** For every coordinate $i$ in the tail dimension, the coefficient of the real-valued associated Boolean function at the singleton frequency containing $i+1$ equals the coefficient of the tail-set indicator at the singleton frequency containing $i$.

**Proof.** First identify the singleton frequency containing $i+1$ with the shifted tail frequency of the singleton containing $i$. The tail-frequency identity (`fourierCoeff_tailFrequency`) reduces the desired coefficient to the average of the two first-coordinate slice coefficients. The slice at first-coordinate sign $1$ is the constant function $1$ (`firstCoordinateSlice_fknOptimalityFunction_one`), whose singleton coefficient is zero: its monomial has expectation zero at a nonempty frequency (`expect_monomial`). The slice at sign $-1$ is $2$ times the tail-set indicator minus $1$ (`firstCoordinateSlice_fknOptimalityFunction_neg_one`). Its singleton coefficient is twice the indicator's coefficient (`fourierCoeff_fknOptimalityLowerSlice_singleton`); combining this with the zero coefficient of the constant slice and the factor of one half gives the claimed identity.

**Key facts.** `FABL.fourierCoeff_tailFrequency`, `FABL.firstCoordinateSlice_fknOptimalityFunction_one`, `FABL.expect_monomial`, `FABL.firstCoordinateSlice_fknOptimalityFunction_neg_one`, `FABL.fourierCoeff_fknOptimalityLowerSlice_singleton`.
