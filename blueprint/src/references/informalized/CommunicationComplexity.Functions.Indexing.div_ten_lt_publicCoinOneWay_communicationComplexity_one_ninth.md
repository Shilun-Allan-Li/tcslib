<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/CommunicationComplexity/DeterministicCC/FuncIndexing/LowerBound.lean :: CommunicationComplexity.Functions.Indexing.div_ten_lt_publicCoinOneWay_communicationComplexity_one_ninth -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Linear Public Coin Lower Bound for Index

**Claim.** For every positive integer $n\ge 300$, the one-way public-coin communication complexity of Index at error $1/9$ is greater than $\lfloor n/10\rfloor$.

**Proof.** First use the large-$n$ distributional lower bound: when $n\ge300$, every deterministic one-way protocol of cost at most $\lfloor n/10\rfloor$ has uniform distributional error greater than $1/9$. The general distributional-to-public-coin lower bound then implies that the public-coin communication complexity at error $1/9$ is strictly greater than this cost threshold.

**Key facts.** `CommunicationComplexity.Functions.Indexing.deterministicOneWayDistributionalLowerBound_one_ninth_of_large`, `CommunicationComplexity.Functions.Indexing.lt_publicCoinOneWay_communicationComplexity_of_distributionalLowerBound`.
