<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter02/InfluencesAndDerivatives/DegreeOneRigidity.lean :: FABL.singletonCoeff_sq_eq_zero_or_one_of_fourierWeightAtMost_one_eq_one -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Singleton Fourier Coefficient Is Boolean

**Claim.** If the Fourier weight on sets of size at most one is $1$, then the square of each singleton Fourier coefficient is either $0$ or $1$.

**Proof.** Fix a coordinate $i$ and evaluate at the all-positive input. The square of the discrete derivative there equals the pivotal indicator, which takes only the values $0$ and $1$ (\texttt{FABL.sq\_discreteDerivative\_toReal\_eq\_pivotalIndicator}). Under the assumed weight condition, the discrete derivative at every input equals the singleton Fourier coefficient for $i$ (\texttt{FABL.discreteDerivative\_toReal\_eq\_singletonCoeff\_of\_fourierWeightAtMost\_one\_eq\_one}). Hence the coefficient's square is either $0$ or $1$.

**Key facts.** `FABL.sq_discreteDerivative_toReal_eq_pivotalIndicator`, `FABL.discreteDerivative_toReal_eq_singletonCoeff_of_fourierWeightAtMost_one_eq_one`.
