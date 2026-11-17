<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/CommunicationComplexity/NewmanTheorem/Entropy/Basic.lean :: ProbabilityTheory.mutualInfo_eq_zero_of_ae_eq_const_right -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Vanishing for a constant second variable

**Claim.** If the second variable is almost everywhere constant, then its mutual information with the first variable is zero.

**Proof.** Mutual information is symmetric in its two variables (`mutualInfo_comm`), so it suffices to consider the constant variable as the first variable. The result then follows from the vanishing theorem for a first variable that is almost everywhere constant (`ProbabilityTheory.mutualInfo_eq_zero_of_ae_eq_const_left`).

**Key facts.** `ProbabilityTheory.mutualInfo_eq_zero_of_ae_eq_const_left`.
