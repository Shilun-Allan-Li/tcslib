<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/CommunicationComplexity/NewmanTheorem/FuncDisjointnessLowerBound/Headline.lean :: CommunicationComplexity.Functions.Disjointness.RandomizedLowerBound.integral_xFiberKL_disjointSpecialYFalse_le_two_mul_gamma_pow_four -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Average Conditional KL Bound

**Claim.** If the total claimed information of the protocol is at most $2\gamma^4/3$, then the stated integral of the conditional KL divergence of Alice’s special-coordinate bit, given $Z$ and under the disjoint-conditioned distribution with Bob’s special bit false, is at most $2\gamma^4$.

**Proof.** The integral is at most $\tfrac32$ times Alice’s information term, by the bound on the integral in terms of Alice’s information (`integral_xFiberKL_disjointSpecialYFalse_le_three_halves_mul_aliceInfoTerm`). Alice’s information term is at most the total claimed information, since the latter is the sum of Alice’s and Bob’s information terms (`aliceInfoTerm_le_claimInfo`). Combining these inequalities with the hypothesis gives an upper bound of $\tfrac32(2\gamma^4/3)=\gamma^4$. Since $\gamma^4\ge 0$, this is at most $2\gamma^4$, as required.

**Key facts.** `CommunicationComplexity.Functions.Disjointness.RandomizedLowerBound.integral_xFiberKL_disjointSpecialYFalse_le_three_halves_mul_aliceInfoTerm`, `CommunicationComplexity.Functions.Disjointness.RandomizedLowerBound.aliceInfoTerm_le_claimInfo`.
