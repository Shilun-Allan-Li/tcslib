<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter02/InfluencesAndDerivatives/DegreeOneRigidity.lean :: FABL.singletonCoeff_sq_eq_zero_or_one_of_fourierWeightAtLevel_one_eq_one -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Singleton Fourier Coefficient Is Boolean

**Claim.** If the Fourier weight at level one is $1$, then the square of each singleton Fourier coefficient is either $0$ or $1$.

**Proof.** Fix a coordinate $i$ and evaluate at the all-positive input. The square of the discrete derivative there equals the pivotal indicator, which is either $0$ or $1$ (\texttt{FABL.sq\_discreteDerivative\_toReal\_eq\_pivotalIndicator}). Under the hypothesis that level-one Fourier weight is $1$, the discrete derivative at every input equals the singleton Fourier coefficient for $i$ (\texttt{FABL.discreteDerivative\_toReal\_eq\_singletonCoeff\_of\_fourierWeightAtLevel\_one\_eq\_one}). Substituting this equality into the squared-derivative identity shows that the coefficient's square is the pivotal indicator, proving the alternatives.

**Key facts.** `FABL.sq_discreteDerivative_toReal_eq_pivotalIndicator`, `FABL.discreteDerivative_toReal_eq_singletonCoeff_of_fourierWeightAtLevel_one_eq_one`.
