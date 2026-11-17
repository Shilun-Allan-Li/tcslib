<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/Randomized/PrimalityMath.lean :: Randomized.exists_not_mem_of_not_sq_dvd -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# A Unit Outside the Euler-Liar Subgroup

**Claim.** For an odd composite integer $N>1$ with no prime square dividing it, there is a unit modulo $N$ outside the subgroup defined by the Jacobi-symbol Euler-liar equation.

**Proof.** Let $p$ be the least prime factor of $N$, and write $N=pm$. The square-free assumption implies $p\nmid m$, so $p$ and $m$ are coprime; also $m>1$ and both factors are odd. Choose a nonsquare residue modulo $p$ and use the Chinese remainder theorem to choose an integer $a$ that equals this nonsquare modulo $p$ and equals $1$ modulo $m$. It is coprime to both factors, hence to $N$, and so determines a unit modulo $N$. Its Jacobi symbol modulo $p$ is $-1$, while modulo $m$ it is $1$; multiplicativity of the Jacobi symbol therefore gives $(a/N)=-1$. If this unit satisfied the Euler-liar equation, reduce that equation modulo $m$. Because $a\equiv1\pmod m$, the right side becomes $1$, whereas the left side is the reduction of $-1$. Thus $-1=1$ modulo $m$, so $m$ divides $2$. This contradicts that $m>1$ is odd. The unit is consequently outside the subgroup. The subgroup membership criterion is `mem_eulerLiarSubgroup`; the conversion of the Jacobi-symbol value to a residue modulo $N$ uses `jacobiSymZMod_natCast`, and coprimality modulo the prime factor is expressed by `coprime_iff_natCast_ne_zero`.

**Key facts.** `Randomized.coprime_iff_natCast_ne_zero`, `Randomized.jacobiSymZMod_natCast`, `Randomized.mem_eulerLiarSubgroup`.
