<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter02/Arrow.lean :: FABL.neg_one_third_le_pow -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Lower bound for powers of negative one third

**Claim.** For every natural number $k$, $-\frac13\leq(-\frac13)^k$.

**Proof.** If $k=0$, the power equals $1$, so the inequality holds. For $k>0$, its absolute value is $(1/3)^k\leq1/3$, since powers of a number in $[0,1]$ do not exceed that number. Thus the power is at least the negative of its absolute value, which is at least $-1/3$.
