<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/Randomized/Fingerprint.lean :: Randomized.primeCounting_le_card_not_dvd -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Prime Count and Nondivisors

**Claim.** If $y\ne0$ and $|y|\le 2^B$, then the number of primes at most $N$ is at most the number of $v<N$ for which $v+1$ does not divide $y$, plus $B$.

**Proof.** Let $P$ be the primes below $N+1$, and let $F$ be the prime factors of $|y|$. The prime-counting identity gives $|P|=\mathrm{primeCounting}(N)$. Since $|y|\ne0$, the bound $2^{|F|}\le |y|\le2^B$ implies $|F|\le B$. Split $P$ into its members outside $F$ and its members in $F$; consequently $|P|\le |P\setminus F|+|F|$. Map each prime $p\in P\setminus F$ to $v=p-1$. Because $p\ge2$, this lies in the range $v<N$. If $v+1$ divided $y$, then the prime $p=v+1$ would divide $|y|$, so it would belong to $F$, a contradiction. The map is injective, since $p-1=q-1$ implies $p=q$. Thus $|P\setminus F|$ is at most the number of eligible nondivisors. Combining the bounds proves the claim.

**Key facts.** `Randomized.two_pow_card_primeFactors_le`.
