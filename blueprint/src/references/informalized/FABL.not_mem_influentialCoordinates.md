<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter09/Friedgut.lean :: FABL.not_mem_influentialCoordinates -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Characterizing Nonmembership in the Influential Set

**Claim.** A coordinate is absent from the set of coordinates whose influence is at least $\tau$ exactly when its influence is strictly less than $\tau$.

**Proof.** By definition, the influential set consists of the coordinates in the full index set satisfying $\tau\leq\operatorname{Inf}_i[f]$. Since $i$ is already an index, its failure to belong to that set is precisely the negation of this inequality, which over the reals is equivalent to $\operatorname{Inf}_i[f]<\tau$.
