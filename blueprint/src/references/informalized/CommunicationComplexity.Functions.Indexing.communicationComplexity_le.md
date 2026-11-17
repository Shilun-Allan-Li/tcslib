<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/CommunicationComplexity/DeterministicCC/FuncIndexing/Basic.lean :: CommunicationComplexity.Functions.Indexing.communicationComplexity_le -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Communication Complexity of Indexing

**Claim.** For every positive integer $n$, the deterministic two-way communication complexity of Indexing on an $n$-bit string and an index in $[n]$ is at most $\lceil\log_2 n\rceil+1$.

**Proof.** The general upper bound for a function with finite input set $Y$ and finite output set $\alpha$ says its deterministic communication complexity is at most $\lceil\log_2|Y|\rceil+\lceil\log_2|\alpha|\rceil$ (CommunicationComplexity.Deterministic.communicationComplexity_le_clog_card_Y_alpha). Here $Y=[n]$ has cardinality $n$, while the Boolean output set has cardinality $2$, whose base-two ceiling logarithm is $1$. Substituting these cardinalities gives the stated bound.

**Key facts.** `CommunicationComplexity.Deterministic.communicationComplexity_le_clog_card_Y_alpha`.
