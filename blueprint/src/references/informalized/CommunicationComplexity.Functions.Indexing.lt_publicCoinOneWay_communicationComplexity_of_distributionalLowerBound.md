<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/CommunicationComplexity/DeterministicCC/FuncIndexing/LowerBound.lean :: CommunicationComplexity.Functions.Indexing.lt_publicCoinOneWay_communicationComplexity_of_distributionalLowerBound -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Distributional Lower Bound Implies Public Coin Lower Bound

**Claim.** If every deterministic one-way protocol of cost at most $c$ has distributional error greater than $\varepsilon$ under the specified uniform input distribution, then the public-coin one-way communication complexity of Index at error $\varepsilon$ is strictly greater than $c$.

**Proof.** Apply the general theorem that a distributional error lower bound for every deterministic protocol of cost at most $c$ implies a public-coin communication-complexity lower bound greater than $c$. Here the function is Index and the distribution is the specified uniform distribution on input pairs, so its hypothesis is exactly the assumption and its conclusion is the claim.

**Key facts.** `CommunicationComplexity.PublicCoin.OneWay.lt_communicationComplexity_of_forall_distributionalError_gt`.
