<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter07/HastadThreeSat.lean :: FABL.oxrAcceptanceProbability_eq_equationSevenSeven -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# OXR Acceptance Identity

**Claim.** For an odd function $f$ with values in $[-1,1]$, the OXR acceptance probability is $\frac34-\frac14\operatorname{Stab}_{-\delta}(f)-\frac14\sum_S\widehat f(S)^2A_\delta(S)$.

**Proof.** For each sampled triple, the OXR predicate’s randomized acceptance value is $\frac34-\frac14\mu_0-\frac14\mu_1\mu_2-\frac14\mu_0\mu_1\mu_2$, where the three means are the values of $f$ at the three query points. Average these four terms separately over the sampled triples. The constant term remains $3/4$. The first query is uniform, so its mean is the empty-set Fourier coefficient; oddness makes that coefficient zero. The product of the second and third query values averages to the noise stability at correlation $-\delta$. The triple product averages to the sum of squared Fourier coefficients weighted by the random-subset Fourier averages. Substituting these evaluations gives the identity.

**Key facts.** `FABL.oxrPredicate_randomizedValue`, `FABL.pmfExpectation_add`, `FABL.pmfExpectation_const`, `FABL.pmfExpectation_const_mul`, `FABL.pmfExpectation_oxrTripleCubePMF_first`, `FABL.pmfExpectation_oxrTripleCubePMF_second_mul_third`, `FABL.pmfExpectation_oxrTripleCubePMF_tripleProduct_eq_randomSubsetAverage`, `FABL.fourierCoeff_even_eq_zero_of_odd`.
