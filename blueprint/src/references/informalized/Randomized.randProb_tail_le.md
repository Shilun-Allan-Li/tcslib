<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/Randomized/Classes.lean :: Randomized.randProb_tail_le -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Upper tail bound for successful blocks

**Claim.** If a block of length $q$ is successful with probability at most $1/2-\varepsilon$, then for a uniformly random word of length $Kq$, the probability that at least half of its $K$ blocks succeed is at most $2(1-4\varepsilon^2)^{\lfloor K/2\rfloor}$.

**Proof.** Write $s$ for the success probability of one block. It satisfies $0\le s\le 1/2-\varepsilon$, hence $s\le 1-s$ and $s(1-s)\le 1/4-\varepsilon^2$. Partition the event of interest according to the exact number $j$ of successful blocks. Since the block count is at most $K$, and the event requires $2j\ge K$, this is a finite sum over those $j\le K$ with $2j\ge K$ (`Randomized.randProb_mem_eq_sum`; `Randomized.blockCount_le`). The exact-count formula (`Randomized.randProb_blockCount`) gives each summand as $\binom Kj s^j(1-s)^{K-j}$. For such $j$, one has $j\ge K-\lfloor K/2\rfloor$. Factor the powers at this balanced threshold: because $s\le1-s$, the excess power of $s$ can be bounded by the same power of $1-s$. This bounds $s^j(1-s)^{K-j}$ by $s^{K-\lfloor K/2\rfloor}(1-s)^{\lfloor K/2\rfloor}$. The parity remainder in $K-\lfloor K/2\rfloor$ contributes a factor at most $1$, since $s\le1$, so the result is at most $[s(1-s)]^{\lfloor K/2\rfloor}$. Bound this by $(1/4-\varepsilon^2)^{\lfloor K/2\rfloor}$ and sum the binomial coefficients over all $j=0,\ldots,K$, whose sum is $2^K$. Finally, writing $K=2\lfloor K/2\rfloor+(K\bmod 2)$ gives $2^K\le 2\cdot4^{\lfloor K/2\rfloor}$. Combining these estimates yields the stated bound.

**Key facts.** `Randomized.randProb_nonneg`, `Randomized.randProb_le_one`, `Randomized.randProb_mem_eq_sum`, `Randomized.blockCount_le`, `Randomized.randProb_blockCount`.
