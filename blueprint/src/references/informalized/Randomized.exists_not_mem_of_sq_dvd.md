<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/Randomized/PrimalityMath.lean :: Randomized.exists_not_mem_of_sq_dvd -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: low -->

# A Unit Outside the Euler-Liar Subgroup

**Claim.** If $N>1$ is odd and a prime square $p^2$ divides $N$, then some unit modulo $N$ lies outside the Euler-liar subgroup.

**Proof.** Write $N=p^2k$ and let $x$ be the residue of $pk$ modulo $N$. Then $x^2=0$ modulo $N$, but $x\ne0$: otherwise $N$ would divide $pk$, which together with $N=p^2k$ would force $p$ to divide $k$ and hence $N$ to divide $pk$ only with the impossible size constraint $p^2k\leq pk$. The binomial recurrence and $x^2=0$ give $(1+x)^j=1+jx$ for every natural number $j$. Moreover, $(1+x)(1-x)=1-x^2=1$, so $1+x$ is a unit. If it belonged to the Euler-liar subgroup, the subgroup consequence `pow_sub_one_eq_one_of_mem_eulerLiarSubgroup` would imply $(1+x)^{N-1}=1$. But the power formula makes this left side $1+(N-1)x$. In $\mathbb Z/N\mathbb Z$, $N-1=-1$, so the equality forces $x=0$, contradicting the construction. Thus this unit is outside the subgroup.

**Key facts.** `Randomized.pow_sub_one_eq_one_of_mem_eulerLiarSubgroup`.

**Caveat.** The source proves $x\ne0$ by using $p\ge2$, $k\ne0$, and the divisibility consequence $N\mid pk\Rightarrow N\le pk$, which contradicts $N=p^2k$; the prose compresses that arithmetic step.
