<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter09/SmallSetExpansion.lean :: FABL.exercise9_6_geometric_square_sum_le -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Geometric square-sum bound

**Claim.** For $0<\delta\le1$ and every natural number $N$, the sum of $(1-\delta)^{2k}$ for $0\le k<N$ is at most $1/\delta^2$.

**Proof.** Set $r=(1-\delta)^2$. Then $0\le r\le1$, and expanding the square shows $\delta^2\le1-r$. The finite geometric-sum identity gives $(\sum_{k=0}^{N-1}r^k)(1-r)=1-r^N$. The sum is nonnegative and $r^N\ge0$, so multiplying the bound $\delta^2\le1-r$ by that sum yields $\delta^2\sum_{k=0}^{N-1}r^k\le1-r^N\le1$. Since $\delta>0$, division by $\delta^2$ gives $\sum r^k\le1/\delta^2$. Finally, $(1-\delta)^{2k}=r^k$, so this is the stated inequality.
