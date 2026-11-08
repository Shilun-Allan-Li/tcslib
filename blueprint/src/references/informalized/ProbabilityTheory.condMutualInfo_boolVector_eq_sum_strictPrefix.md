<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/CommunicationComplexity/NewmanTheorem/Entropy/ChainRules.lean :: ProbabilityTheory.condMutualInfo_boolVector_eq_sum_strictPrefix -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Boolean Vector Chain Rule

**Claim.** The conditional mutual information between a finite Boolean vector and a random variable, given another random variable, is the sum of the conditional mutual informations of its coordinates given the preceding coordinates and the conditioning variable.

**Proof.** Proceed by induction on the vector length. For length zero, the vector is constant, so its conditional mutual information vanishes by the zero-information property for a constant variable (`condMutualInfo_eq_zero_of_ae_eq_const_left`); the empty sum is also zero. For a vector of length $m+1$, separate its first $m$ coordinates from its last coordinate. This splitting is an injective recoding of the original vector, so it preserves conditional mutual information. Apply the two-variable chain rule (`condMutualInfo_prod_left_eq_add`) to express the information of the pair as the information of the first $m$ coordinates plus the information of the last coordinate conditioned on those first coordinates and $Z$. Apply the induction hypothesis to the first term. Finally, reindex the sum over the first $m$ coordinates together with the last-coordinate term as the sum over all $m+1$ coordinates; the conditioning prefix in each term is exactly the strict prefix specified in the statement.

**Key facts.** `ProbabilityTheory.condMutualInfo_eq_zero_of_ae_eq_const_left`, `ProbabilityTheory.condMutualInfo_prod_left_eq_add`.
