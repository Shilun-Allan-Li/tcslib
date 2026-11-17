<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/Randomized/ZPPHostsClasses.lean :: Randomized.succ_pow_le_two_pow_mul -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Shifted natural number power bound

**Claim.** For all natural numbers $n,p$, $(n+1)^p\le 2^p(n^p+1)$.

**Proof.** If $n=0$, both sides simplify to $1$ and $2^p$, respectively, and $1\le2^p$. If $n>0$, then $n+1\le2n$, so raising to the power $p$ gives $(n+1)^p\le(2n)^p=2^pn^p$. Since $n^p\le n^p+1$, multiplication by the nonnegative factor $2^p$ proves the claimed bound.
