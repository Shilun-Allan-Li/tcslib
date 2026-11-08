<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/CommunicationComplexity/DeterministicCC/FuncIndexing/LowerBound.lean :: CommunicationComplexity.Functions.Indexing.div_ten_lt_publicCoinOneWay_communicationComplexity_of_distributionalLowerBound -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Public Coin Lower Bound from Distributional Error

**Claim.** If every deterministic one-way protocol of cost at most $\lfloor n/10\rfloor$ has distributional error greater than $1/8$ under the uniform input distribution, then the public-coin one-way communication complexity of Index at error $1/8$ is greater than $\lfloor n/10\rfloor$.

**Proof.** Apply the general distributional-to-public-coin lower bound to the stated hypothesis, with error $1/8$ and cost threshold $\lfloor n/10\rfloor$. That result gives the strict lower bound directly.

**Key facts.** `CommunicationComplexity.Functions.Indexing.lt_publicCoinOneWay_communicationComplexity_of_distributionalLowerBound`.
