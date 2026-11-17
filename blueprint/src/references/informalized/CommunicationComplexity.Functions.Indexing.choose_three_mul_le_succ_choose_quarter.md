<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/CommunicationComplexity/DeterministicCC/FuncIndexing/LowerBound.lean :: CommunicationComplexity.Functions.Indexing.choose_three_mul_le_succ_choose_quarter -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Growth of Binomial Coefficients Below a Quarter

**Claim.** If $i<\lfloor n/4\rfloor$, then $3\binom{n}{i}\le\binom{n}{i+1}$.

**Proof.** Since $i<\lfloor n/4\rfloor$, we have $i+1\le\lfloor n/4\rfloor$, and therefore $4(i+1)\le n$. In particular, $3(i+1)\le n-i$. Multiply this inequality by $\binom{n}{i}$, which is nonnegative. The binomial absorption identity $(i+1)\binom{n}{i+1}=(n-i)\binom{n}{i}$ then gives $(i+1)3\binom{n}{i}\le(i+1)\binom{n}{i+1}$. Because $i+1>0$, cancel this factor to obtain the result.
