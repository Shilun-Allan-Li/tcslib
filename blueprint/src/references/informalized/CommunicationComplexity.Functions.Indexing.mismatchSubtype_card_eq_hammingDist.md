<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/CommunicationComplexity/DeterministicCC/FuncIndexing/LowerBound.lean :: CommunicationComplexity.Functions.Indexing.mismatchSubtype_card_eq_hammingDist -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Mismatch Count Equals Hamming Distance

**Claim.** For a deterministic one-way protocol and input $x$, the number of indices where the protocol’s output differs from Index equals the Hamming distance from $x$ to the answer vector determined by the message sent on $x$.

**Proof.** The mismatch indices form the subtype of indices $i$ satisfying $p.\mathrm{decode}(p.\mathrm{send}(x),i)\ne x_i$. The answer vector has coordinate $i$ equal to $p.\mathrm{decode}(p.\mathrm{send}(x),i)$. Thus this subtype is exactly the set of coordinates where $x$ differs from that answer vector. By the definition of Hamming distance as the cardinality of the disagreement set, the two quantities are equal.
