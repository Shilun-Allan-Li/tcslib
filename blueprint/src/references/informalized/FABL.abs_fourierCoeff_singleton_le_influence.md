<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter05/UnateFunctions.lean :: FABL.abs_fourierCoeff_singleton_le_influence -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Singleton Fourier coefficient and influence

**Claim.** For every Boolean function on the sign cube and every coordinate, the absolute value of its singleton Fourier coefficient is at most its influence at that coordinate.

**Proof.** The mean of the discrete derivative in coordinate $i$ equals the Fourier coefficient indexed by $\{i\}$ (\texttt{FABL.mean\_discreteDerivative\_eq\_fourierCoeff\_singleton}). Thus it suffices to bound the absolute value of this mean. The triangle inequality for finite expectations bounds it by the expectation of the absolute value of the derivative. Since the function takes only sign values, the absolute value of its discrete derivative equals its square at every point (\texttt{FABL.abs\_discreteDerivative\_toReal\_eq\_sq}). The expectation of that square is exactly the influence, proving the claim.

**Key facts.** `FABL.mean_discreteDerivative_eq_fourierCoeff_singleton`, `FABL.abs_discreteDerivative_toReal_eq_sq`.
