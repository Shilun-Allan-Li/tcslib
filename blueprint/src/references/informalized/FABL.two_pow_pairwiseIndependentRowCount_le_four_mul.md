<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter06/Constructions/PairwiseIndependence.lean :: FABL.two_pow_pairwiseIndependentRowCount_le_four_mul -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Bound on the number of rows

**Claim.** For every positive integer $n$, if $r$ is the least nonnegative integer with $n+1\le 2^r$ and $m=\max\{1,r\}$, then $2^m\le 4n$.

**Proof.** Because $n>0$, we have $1<n+1$, so $r=\operatorname{clog}_2(n+1)$ is positive and hence $m=r$. The predecessor property of the ceiling logarithm gives $2^{r-1}<n+1$. Since $r>0$, $r=(r-1)+1$, and therefore $2^r=2^{r-1}\cdot2\le 2(n+1)$. For positive integer $n$, $2(n+1)\le4n$, proving the bound.
