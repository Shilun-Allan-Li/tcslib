<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/CommunicationComplexity/DeterministicCC/FuncIndexing/LowerBound.lean :: CommunicationComplexity.Functions.Indexing.goodInput_card_le -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Counting Inputs Near Answer Vectors

**Claim.** For a deterministic one-way Index protocol, the number of inputs within Hamming distance less than $n/4$ of some answer vector is at most $|A|\,2\binom{n}{\lfloor n/4\rfloor}$, where $A$ is the set of answer vectors.

**Proof.** Every input counted as good is, by definition, within real Hamming distance less than $n/4$ of some answer vector. Since Hamming distance is an integer, this places it within distance at most $\lfloor n/4\rfloor$; symmetry of Hamming distance puts it in the corresponding ball centered at that answer vector. Thus the good inputs lie in the union of these balls. The cardinality of a union is at most the sum of the cardinalities of its constituent sets, and each quarter-radius binary Hamming ball has size at most $2\binom{n}{\lfloor n/4\rfloor}$ by the quarter-radius ball bound. Multiplying that per-ball bound by the number of answer vectors proves the result.

**Key facts.** `CommunicationComplexity.Functions.Indexing.hammingBall_card_quarter_le_two_mul_choose`.
