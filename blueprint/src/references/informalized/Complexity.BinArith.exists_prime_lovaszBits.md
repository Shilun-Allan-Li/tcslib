<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/ClassP/BinaryArith/PrimeFind.lean :: Complexity.BinArith.exists_prime_lovaszBits -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Prime in a Dyadic Interval

**Claim.** For every natural number $n$, there is a prime number $p$ strictly greater than $2^{\ell(n)}$ and at most $2^{\ell(n)+1}$, where $\ell(n)$ is the least natural number $k$ such that $2^k\ge 2n$.

**Proof.** Set $k=\ell(n)$. Bertrand's prime interval theorem, in the form that for every positive integer $N$ there is a prime $p$ with $N<p\le 2N$, applied to $N=2^k$, gives a prime satisfying $2^k<p\le 2\cdot2^k$. Since $2^k$ is positive, the theorem applies. Finally, $2\cdot2^k=2^{k+1}$, so this prime has the required bounds.
