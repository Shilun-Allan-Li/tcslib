<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/ClassP/BinaryArith/PrimeFind.lean :: Complexity.BinArith.searchInv_step -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Search Invariant and Progress

**Claim.** Under the stated search invariant, one search step preserves the invariant, strictly decreases the search measure when it is positive, and leaves the string unchanged when the measure is zero.

**Proof.** Write $P$ for the least prime above the specified threshold. First split on the final marker bit $b$. If $b=1$, the invariant forces $c=P$, and the search step leaves the encoded string unchanged. The measure is zero in this case, so the required implications follow. Now suppose $b=0$. The measure is $(P-c)(P+1)+(c-d)+1$, which is positive since $c\le P$ and $d\le c$.

If $d=c$, the divisibility condition says that $c$ has no proper divisor at least $2$, so $c$ is prime. Since $c$ lies above the threshold and at most $P$, the least-prime property forces $c=P$. The equality test therefore changes only the marker from $0$ to $1$. The invariant holds with $c=d=P$, and the new measure is zero, hence strictly smaller.

Otherwise $d<c$. If $d$ divides $c$, then $c<P$: equality would make $d$ a proper divisor of the prime $P$, contrary to $d\ge2$. The step increments $c$ and resets $d$ to $2$, keeping the marker false. These values satisfy the invariant: the new first value remains at most $P$, and no integer in the interval from $2$ up to but not including $2$ can divide it. In the measure, the first term decreases by $P+1$ while the difference term increases by at most $P$, so the measure strictly decreases.

If $d$ does not divide $c$, the step keeps $c$ and replaces $d$ by $d+1$, again with false marker. The old divisibility condition rules out divisors below $d$, and the failed divisibility test rules out $d$ itself; thus the condition holds below $d+1$. The invariant is preserved, and the measure decreases because $c-(d+1)<c-d$. In both branches the old measure was positive, so the implication concerning measure zero is vacuous.

**Key facts.** `Complexity.LogProg.bitsVal_bits`, `Complexity.BinArith.lovaszPrime_prime`, `Complexity.BinArith.not_prime_of_lt_lovaszPrime`, `Complexity.pairFstD_pairEncode`, `Complexity.pairSndD_pairEncode`.
