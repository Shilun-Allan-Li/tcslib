<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/CommunicationComplexity/NewmanTheorem/FuncDisjointnessLowerBound/Headline.lean :: CommunicationComplexity.Functions.Disjointness.RandomizedLowerBound.lt_publicCoin_communicationComplexity_disjointness_of_lt_const_mul_n -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Public-Coin Communication Lower Bound

**Claim.** If the integer $k$ is strictly below the stated constant multiple of $n$, then public-coin communication complexity for set disjointness with error at most $1/32$ is greater than $k$.

**Proof.** Use the public-coin distributional lower-bound principle: it suffices to show that every deterministic protocol of complexity at most $k$ has error greater than $1/32$ under the specified input distribution (`CommunicationComplexity.PublicCoin.lt_communicationComplexity_of_forall_distributionalError_gt`). Suppose instead that such a protocol has distributional error at most $1/32$. The deterministic lower bound then says its complexity is at least $((1/32768)^2)n/(3\log 2)$ (`const_mul_n_le_complexity_of_distributionalError_le`). But complexity at most $k$, while the hypothesis makes $k$ strictly smaller than this quantity. These inequalities contradict one another, proving the claim.

**Key facts.** `CommunicationComplexity.PublicCoin.lt_communicationComplexity_of_forall_distributionalError_gt`, `CommunicationComplexity.Functions.Disjointness.RandomizedLowerBound.const_mul_n_le_complexity_of_distributionalError_le`.
