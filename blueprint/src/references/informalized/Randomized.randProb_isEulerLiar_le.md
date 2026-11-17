<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/Randomized/PrimalityMath.lean :: Randomized.randProb_isEulerLiar_le -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Euler-Liar Probability Bound

**Claim.** For odd composite $N>1$, the probability that a uniformly random Boolean word of length $\ell$ produces an Euler liar under the stated sampling rule is at most $\frac12+\frac{N-1}{2^{\ell+1}}$.

**Proof.** Put $K=N-1$, and let $S$ be the set of Euler-liar samples in the interval $[1,N)$. The bound on the number of Euler liars gives $2|S|\le K$ (`Randomized.two_mul_card_filter_isEulerLiar_le`). Let $F$ be the set of Boolean words of length $\ell$ whose sampled values are liars. Map each such word to the pair consisting of its sample $1+v\bmod K$ and the quotient $\lfloor v/K\rfloor$, where $v$ is the binary value of the word. The sample lies in $S$ (`Randomized.eulerSample_mem_Ico`); moreover, $v<2^\ell$ (`Complexity.LogProg.bitsVal_lt_two_pow`), so the quotient is among the first $\lfloor 2^\ell/K\rfloor+1$ nonnegative integers. This map is injective: equality of the pair gives equality of the remainders from the sample and equality of the quotients, hence equality of the binary values by quotient-remainder reconstruction. Binary values distinguish Boolean words of a fixed length (`Complexity.LogProg.eq_of_bitsVal_eq`). Thus $|F|\le |S|(\lfloor 2^\ell/K\rfloor+1)$. Combining this with $2|S|\le K$ and $K\lfloor 2^\ell/K\rfloor\le2^\ell$ yields $2|F|\le2^\ell+K$. Dividing by the total number $2^\ell$ of Boolean words gives the claimed probability bound, since $K=N-1$.

**Key facts.** `Randomized.two_mul_card_filter_isEulerLiar_le`, `Randomized.eulerSample_mem_Ico`, `Complexity.LogProg.bitsVal_lt_two_pow`, `Complexity.LogProg.eq_of_bitsVal_eq`.
