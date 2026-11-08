<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/CommunicationComplexity/DeterministicCC/FuncIndexing/LowerBound.lean :: CommunicationComplexity.Functions.Indexing.div_nat_div_four_le_101_25 -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# A Bound on the Quarter-Divisor Ratio

**Claim.** For every natural number $n\ge300$, the ratio $n/\lfloor n/4\rfloor$ is at most $101/25$.

**Proof.** Set $k=\lfloor n/4\rfloor$. The assumption $n\ge300$ implies $k\ge75$, so $k>0$. Write $n=4k+r$, where the remainder $r=n\bmod4$ satisfies $0\le r\le3$. Then $n/k=4+r/k\le4+3/k\le4+3/75=101/25$.
