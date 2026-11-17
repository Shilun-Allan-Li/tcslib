<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter03/GoldreichLevinAlgorithm/Resources.lean :: FABL.goldreichLevinCallConfidence_failureBits_le -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Failure-Bit Bound

**Claim.** For $A=\lceil4/\tau^2\rceil$ and $\delta=1/[40(n+1)(A+1)]$, the failure-bit count $\operatorname{clog}_2(\lceil2/\delta\rceil)$ is at most $80(n+1)(A+1)$.

**Proof.** Set $N=80(n+1)(A+1)$. Substituting the stated value of $\delta$ gives $2/\delta=N$, which is already a natural number. Its ceiling is therefore $N$. Finally, $N\le2^N$; the defining ceiling-logarithm bound for the least exponent whose power of two reaches the argument then gives $\operatorname{clog}_2(N)\le N$, as required.
