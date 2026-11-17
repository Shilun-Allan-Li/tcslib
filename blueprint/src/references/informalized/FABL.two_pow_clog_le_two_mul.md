<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter09/LearningConsequencesResources.lean :: FABL.two_pow_clog_le_two_mul -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Binary ceiling logarithm bound

**Claim.** For every positive natural number $x$, the power $2^{\operatorname{clog}_2(x)}$ is at most $2x$.

**Proof.** If $x=1$, then $\operatorname{clog}_2(1)=0$, so the inequality reads $1\le2$. Otherwise $x>1$. The defining property of the binary ceiling logarithm gives $2^{\operatorname{clog}_2(x)-1}<x$. Since the exponent is a predecessor, the successor-power identity yields $2^{\operatorname{clog}_2(x)}=2^{\operatorname{clog}_2(x)-1}\cdot2$. Thus this power is at most $2x$.
