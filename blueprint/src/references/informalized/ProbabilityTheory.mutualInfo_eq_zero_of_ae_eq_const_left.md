<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/CommunicationComplexity/NewmanTheorem/Entropy/Basic.lean :: ProbabilityTheory.mutualInfo_eq_zero_of_ae_eq_const_left -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Mutual information with a constant variable

**Claim.** If the first variable is almost everywhere constant, its mutual information with the second variable is zero.

**Proof.** The constant random variable is independent of every random variable (`indepFun_const_left`). Independence is preserved when either variable is replaced by an almost-everywhere equal one, so $X$ and $Y$ are independent. Independent variables have zero mutual information, giving the result.
