<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/CommunicationComplexity/DeterministicCC/FuncIndexing/LowerBound.lean :: CommunicationComplexity.Functions.Indexing.hammingBall_card_quarter_le_two_mul_choose -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Quarter-Radius Hamming Ball Bound

**Claim.** For every natural number $n$ and binary word $a$ of length $n$, the Hamming ball centered at $a$ with radius $\lfloor n/4\rfloor$ has cardinality at most $2\binom{n}{\lfloor n/4\rfloor}$.

**Proof.** Write $r=\lfloor n/4\rfloor$ and $b_i=\binom{n}{i}$. For each $i<r$, the successive-binomial estimate gives $3b_i\le b_{i+1}$, hence $2b_i\le b_{i+1}-b_i$. Summing over $i<r$ telescopes to $2\sum_{i<r}b_i\le b_r-b_0\le b_r$. Adding the final term $b_r$ shows that $\sum_{i\le r}b_i\le2b_r$. The binary Hamming-ball volume formula identifies the ball’s cardinality with this partial binomial sum, yielding the claimed bound.

**Key facts.** `CommunicationComplexity.Functions.Indexing.choose_three_mul_le_succ_choose_quarter`, `CommunicationComplexity.ballVol_binary`, `CommunicationComplexity.hammingBall_card`.
