<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter09/MatchingAsymptotics.lean :: FABL.tendsto_fixedShiftFactorialRatio -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Fixed-Shift Factorial Ratio Limit

**Claim.** For each natural number $d$, the finite product $\prod_{i=0}^{3d-1}\frac{m+i+1}{m+3d+i+1}$ tends to $1$ as $m\to\infty$.

**Proof.** Fix an index $i$ in the finite product and write its denominator as $D_m=m+3d+i+1$. This denominator tends to infinity, so $3d/D_m\to0$. The factor can be written as $1-3d/D_m$, and hence tends to $1$. Since the product has only finitely many factors, the limit of the product is the product of their limits, namely $1$.
