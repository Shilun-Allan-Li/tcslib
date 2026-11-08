<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter02/Arrow.lean :: FABL.neg_three_fourths_mul_neg_one_third_pow_le -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Geometric-term upper bound

**Claim.** For every natural number $k$, $(-3/4)(-1/3)^k\leq1/36+(2/9)\mathbf{1}_{\{k=1\}}$.

**Proof.** When $k=1$, direct evaluation gives equality. Suppose $k\ne1$, so the indicator term vanishes. If $k$ is even, $(-1/3)^k\geq0$, and multiplication by $-3/4$ gives a nonpositive quantity, hence one at most $1/36$. If $k$ is odd, write $k=2j+1$. Since $k\ne1$, this forces $k\geq3$. The odd power is $-(1/3)^k$, and $(1/3)^k\leq(1/3)^3=1/27$. Therefore $(-3/4)(-1/3)^k=(3/4)(1/3)^k\leq(3/4)(1/27)=1/36$.
