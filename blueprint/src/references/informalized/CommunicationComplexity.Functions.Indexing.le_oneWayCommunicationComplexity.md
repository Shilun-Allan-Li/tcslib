<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/CommunicationComplexity/DeterministicCC/FuncIndexing/Basic.lean :: CommunicationComplexity.Functions.Indexing.le_oneWayCommunicationComplexity -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Deterministic Indexing Communication Lower Bound

**Claim.** The deterministic one-way communication complexity of Index on $n$-bit strings is at least $n$.

**Proof.** Use the characterization of a lower bound on deterministic communication complexity: it suffices to show that every protocol computing Index correctly has cost at least $n$. For such a protocol, Alice’s message map must be injective. Indeed, if two inputs $x$ and $y$ produced the same message, Bob would give the same answer on every index for both inputs; correctness says those answers are respectively $x_i$ and $y_i$, so $x_i=y_i$ for every $i$, hence $x=y$. There are $2^n$ possible inputs, so injectivity requires at least $2^n$ messages. A protocol of cost $c=\lceil\log_2 |M|\rceil$ has at most $2^c$ messages. Therefore $2^n\le2^c$, which forces $n\le c$. Since this holds for every correct protocol, the communication complexity is at least $n$.

**Key facts.** `CommunicationComplexity.Deterministic.OneWay.le_communicationComplexity_iff`.
