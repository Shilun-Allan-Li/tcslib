<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/CommunicationComplexity/DeterministicCC/FuncIndexing/LowerBound.lean :: CommunicationComplexity.Functions.Indexing.badInput_implies_hammingDist_ge -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Bad Inputs Are Far from Every Answer

**Claim.** For a bad input $x$, the answer vector produced by the message sent on $x$ has Hamming distance at least $n/4$ from $x$.

**Proof.** The answer vector produced by the message sent on $x$ belongs to the answer set, since that set consists of the answer vectors of all messages. If its Hamming distance from $x$ were less than $n/4$, it would therefore witness that $x$ is not bad. This contradicts the definition of a bad input, so the distance is at least $n/4$.
