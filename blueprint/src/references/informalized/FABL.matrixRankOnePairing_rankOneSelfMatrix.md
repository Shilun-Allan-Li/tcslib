<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter07/AlgebraicPCPP.lean :: FABL.matrixRankOnePairing_rankOneSelfMatrix -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Pairing with a rank-one matrix

**Claim.** Let $n$ be a natural number and let $\gamma,x,y\in\mathbb{F}_2^n$. Pairing the matrix with entries $\gamma_i\gamma_j$ against $x$ and $y$ gives $(\gamma\cdot x)(\gamma\cdot y)$ in $\mathbb{F}_2$.

**Proof.** Expanding the definitions, the pairing is $\sum_i\sum_j \gamma_i\gamma_j(x_i y_j)$. For each fixed $i$, rearrange the factors and distribute the factor $\gamma_i x_i$ across the inner sum to write this as $\sum_i (\gamma_i x_i)\sum_j(\gamma_j y_j)$. The inner sum is independent of $i$, so factoring it out gives $(\sum_i\gamma_i x_i)(\sum_j\gamma_j y_j)$. These two sums are the dot products $\gamma\cdot x$ and $\gamma\cdot y$, respectively.
