<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter02/InfluencesAndDerivatives/DegreeOneRigidity.lean :: FABL.eq_dictator_or_neg_dictator_of_fourierWeightAtLevel_one_eq_one -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Boolean function with level-one weight one

**Claim.** If a Boolean-valued function has Fourier weight one at level one, then it is either a dictator or the negative of a dictator for some coordinate.

**Proof.** The level-one weight condition yields a coordinate i whose singleton Fourier coefficient has square 1, while every other singleton coefficient is zero (`FABL.exists_unique_singletonCoeff_sq_eq_one`). Hence the coefficient at i is either 1 or −1. The level-one Fourier expansion expresses the function as the sum of its singleton coefficients times the corresponding coordinate signs (`FABL.toReal_eq_sum_singleton_of_fourierWeightAtLevel_one_eq_one`); all terms except the i-th vanish. Therefore its real-valued form is either x ↦ x_i or x ↦ −x_i. Since `signValue` is injective (`FABL.signValue_injective`), these equalities of real-valued forms give, respectively, equality with the dictator or with its negative as Boolean functions.

**Key facts.** `FABL.exists_unique_singletonCoeff_sq_eq_one`, `FABL.toReal_eq_sum_singleton_of_fourierWeightAtLevel_one_eq_one`, `FABL.signValue_injective`.
