<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter05/FourierCoefficientsOfMajority.lean :: FABL.exercise5_24 -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Inverse-square-root inequality

**Claim.** For natural numbers $k,n$ with $1\le k$ and $2k\le n$, the stated inverse-square-root expression is at most $1+2k/n$.

**Proof.** Set $x=k/n$ and $y=1/n$, and write $A=(1-x)(1-y)$. The hypotheses imply $n>0$, $0\le y\le x\le1/2$, so both factors defining $A$ are positive. Since $1-y\ge1-x$, we have $(1-x)^2\le A$, and therefore $1-x\le\sqrt A$. Taking reciprocals of positive quantities gives $A^{-1/2}\le(1-x)^{-1}$. Also $(1-x)^{-1}\le1+2x$: after multiplying by $1-x>0$, this is equivalent to $0\le x(1-2x)$, which follows from $0\le x\le1/2$. Finally, direct algebra shows that the expression inside the original power is $A$, and $A^{-1/2}=1/\sqrt A$. Substituting $x=k/n$ proves the inequality.
