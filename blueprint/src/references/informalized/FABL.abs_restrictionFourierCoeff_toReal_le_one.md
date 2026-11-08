<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter06/LearningAndTesting/RestrictedWeightAlgorithm.lean :: FABL.abs_restrictionFourierCoeff_toReal_le_one -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Restricted Fourier Coefficient Bound

**Claim.** For every fixed assignment on the complementary coordinates, the absolute value of the restricted Fourier coefficient of a Boolean function is at most $1$.

**Proof.** The restricted coefficient is the uniform average over the free coordinates of the restricted function multiplied by the corresponding character. The absolute value of an average is at most the average of the absolute values. At each point, the function takes a sign value, whose absolute value is $1$, and the character, being a product of sign values, also has absolute value $1$. Thus every integrand has absolute value $1$, so its average absolute value is $1$.

**Key facts.** `FABL.signRestriction_apply`, `FABL.abs_signValue_eq_one`, `FABL.abs_indexedMonomial_eq_one'`.
