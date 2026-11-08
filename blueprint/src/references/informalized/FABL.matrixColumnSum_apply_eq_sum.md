<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter06/Constructions/VandermondeConstruction.lean :: FABL.matrixColumnSum_apply_eq_sum -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Matrix Column Sum Formula

**Claim.** For an $m\times n$ matrix $H$ over $\mathbb F_2$, a set $S$ of column indices, and a row index $i$, the $i$th coordinate of the sum of the columns indexed by $S$ is $\sum_{j\in S}H_{ij}$.

**Proof.** The matrix-vector product defining the column sum has $i$th coordinate $\sum_j H_{ij}c_j$, where $c_j$ is the indicator of membership in $S$, viewed in $\mathbb F_2$. Each term is $H_{ij}$ when $j\in S$ and zero otherwise. Filtering the full finite sum to the indices in $S$ therefore gives precisely $\sum_{j\in S}H_{ij}$.

**Key facts.** `FABL.f₂CubeOfFinset_apply`.
