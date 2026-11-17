<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter02/InfluencesAndDerivatives/DegreeOneRigidity.lean :: FABL.discreteDerivative_toReal_eq_singletonCoeff_of_fourierWeightAtLevel_one_eq_one -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Derivative as a Singleton Fourier Coefficient

**Claim.** If the total Fourier weight at level one of the real-valued Boolean function is $1$, then its discrete derivative in coordinate $i$ at every cube point equals its Fourier coefficient on $\{i\}$.

**Proof.** Express the discrete derivative as the sum over all subsets $S$ containing $i$ of the Fourier coefficient on $S$ times the monomial on $S$ with $i$ removed (`discreteDerivative_eq_fourier_sum`). In this sum, the singleton $S=\{i\}$ contributes the Fourier coefficient on $\{i\}$, since the monomial on the empty set is $1$. Every other contributing set contains $i$ and is not a singleton, so its Fourier coefficient vanishes by the level-one weight hypothesis (`fourierCoeff_eq_zero_of_fourierWeightAtLevel_one_eq_one`). Thus only the singleton term remains.

**Key facts.** `FABL.discreteDerivative_eq_fourier_sum`, `FABL.fourierCoeff_eq_zero_of_fourierWeightAtLevel_one_eq_one`.
