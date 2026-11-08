<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter02/InfluencesAndDerivatives/DegreeOneRigidity.lean :: FABL.discreteDerivative_toReal_eq_singletonCoeff_of_fourierWeightAtMost_one_eq_one -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Derivative as a Singleton Fourier Coefficient

**Claim.** If the total Fourier weight on subsets of size at most one of the real-valued Boolean function is $1$, then its discrete derivative in coordinate $i$ at every cube point equals its Fourier coefficient on $\{i\}$.

**Proof.** Write the derivative as a sum over sets $S$ containing $i$, with summand the Fourier coefficient on $S$ times the monomial on $S$ with $i$ removed (`discreteDerivative_eq_fourier_sum`). The singleton set $\{i\}$ contributes its Fourier coefficient, because the empty-set monomial is $1$. For any other set in the sum, containing $i$ forces its size to be positive, and being different from $\{i\}$ forces its size to exceed one. Its Fourier coefficient therefore vanishes under the weight-at-most-one hypothesis (`fourierCoeff_eq_zero_of_fourierWeightAtMost_one_eq_one`). The sum reduces to the claimed singleton coefficient.

**Key facts.** `FABL.discreteDerivative_eq_fourier_sum`, `FABL.fourierCoeff_eq_zero_of_fourierWeightAtMost_one_eq_one`.
