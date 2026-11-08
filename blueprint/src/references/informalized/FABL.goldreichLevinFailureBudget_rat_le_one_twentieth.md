<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter03/GoldreichLevinAlgorithm/Adaptive.lean :: FABL.goldreichLevinFailureBudget_rat_le_one_twentieth -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Goldreich–Levin failure budget

**Claim.** For the active cap $A=\lceil4/\tau^2\rceil$ and confidence parameter $\delta=1/[40(n+1)(A+1)]$, one has $n(2A)\delta\le1/20$.

**Proof.** Write $A$ for the active cap and $D=40(n+1)(A+1)$ for the positive denominator defining the confidence parameter, so that $\delta=1/D$. Since $n,A\ge0$, we have $nA\le(n+1)(A+1)$. Rewriting the left side gives $2nA/D$. The preceding product bound makes this at most $2(n+1)(A+1)/[40(n+1)(A+1)]=1/20$.
