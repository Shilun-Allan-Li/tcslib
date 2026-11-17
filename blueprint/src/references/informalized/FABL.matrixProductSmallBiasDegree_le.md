<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter06/LearningAndTesting/MatrixProductVerification.lean :: FABL.matrixProductSmallBiasDegree_le -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Small-bias degree bound

**Claim.** For every natural number $n$, the matrix-product small-bias degree is at most $2+\lceil\log_2(n+1)\rceil$.

**Proof.** By definition, the degree is the maximum of $1$ and $\operatorname{clog}_2(3n)$. The first entry is at most the claimed bound since that bound is at least $2$. For the second entry, the characterization of the ceiling logarithm reduces the desired inequality to $3n\le 2^{2+\operatorname{clog}_2(n+1)}$. Since $3n\le4(n+1)$ and $n+1\le2^{\operatorname{clog}_2(n+1)}$, we have $3n\le4\cdot2^{\operatorname{clog}_2(n+1)}=2^{2+\operatorname{clog}_2(n+1)}$, as required.
