<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/CommunicationComplexity/DeterministicCC/FuncIndexing/LowerBound.lean :: CommunicationComplexity.Functions.Indexing.choose_quarter_le_eleven_pow -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# A Quarter Binomial Coefficient Bound

**Claim.** For every natural number $n\ge 300$, the binomial coefficient $\binom{n}{\lfloor n/4\rfloor}$ is at most $11^{\lfloor n/4\rfloor}$.

**Proof.** Put $k=\lfloor n/4\rfloor$. The hypothesis ensures $k>0$. First use the standard estimate $\binom{n}{k}\le n^k/k!$. Stirling's lower bound gives $k!\ge \sqrt{2\pi k}(k/e)^k$, and since $k\ge1$ and $\pi>3$, the square-root factor is at least $1$. Hence $k!\ge(k/e)^k$, so the binomial coefficient is at most $(e n/k)^k$. The ratio bound $n/k\le101/25$ (CommunicationComplexity.Functions.Indexing.div_nat_div_four_le_101_25) and the estimate $e\le68/25$ (CommunicationComplexity.Functions.Indexing.exp_one_le_68_div_25) imply $e n/k\le(68/25)(101/25)\le11$. Raising these nonnegative quantities to the power $k$ yields the claimed bound.

**Key facts.** `CommunicationComplexity.Functions.Indexing.div_nat_div_four_le_101_25`, `CommunicationComplexity.Functions.Indexing.exp_one_le_68_div_25`.
