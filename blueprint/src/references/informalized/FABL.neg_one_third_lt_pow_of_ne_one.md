<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter02/Arrow.lean :: FABL.neg_one_third_lt_pow_of_ne_one -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Strict lower bound for powers

**Claim.** For every natural number $k\ne1$, one has $-\frac13<(-\frac13)^k$.

**Proof.** For $k=0$, the power is $1$, giving the strict inequality. The case $k=1$ is excluded. Thus the remaining case has $k\geq2$. Its absolute value is $(1/3)^k<1/3$, because a positive power with exponent at least two strictly decreases the value $1/3$. The power is at least the negative of its absolute value, which is therefore strictly greater than $-1/3$.
