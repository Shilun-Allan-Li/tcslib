<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter05/AverageInfluence.lean :: FABL.natCast_mul_one_sub_pow_le -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Power Inequality for Bounded Exponents

**Claim.** If $0\le a\le1$ and $k\le n$, then $k(1-a^n)\le n(1-a^k)$.

**Proof.** If $k=0$, both sides are zero. Suppose $k>0$. For each $j<k$, the assumptions on $a$ imply $a^k\le a^j$, so summing gives $k a^k\le\sum_{j=0}^{k-1}a^j$. Multiplying by $1-a\ge0$ and using the geometric-sum identity yields $k a^k(1-a)\le1-a^k$. Next, Bernoulli's inequality gives $1-a^{n-k}\le(n-k)(1-a)$. Multiply this by the nonnegative quantity $k a^k$ and combine it with the preceding bound, multiplied by $n-k\ge0$, to obtain $k a^k(1-a^{n-k})\le(n-k)(1-a^k)$. Finally, use $n=k+(n-k)$ and $a^n=a^k a^{n-k}$; rearranging the resulting inequality gives $k(1-a^n)\le n(1-a^k)$.
