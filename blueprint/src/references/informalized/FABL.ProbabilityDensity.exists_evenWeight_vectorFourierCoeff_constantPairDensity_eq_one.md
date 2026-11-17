<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter06/Pseudorandomness/SmallBias.lean :: FABL.ProbabilityDensity.exists_evenWeight_vectorFourierCoeff_constantPairDensity_eq_one -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# A Weight-Two Fourier Coefficient

**Claim.** If $n\ge2$, there is a nonzero vector $\gamma\in\mathbb F_2^n$ whose support has cardinality $2$ and whose vector Fourier coefficient with respect to the constant-pair probability density is $1$.

**Proof.** Choose the first two coordinates $i=0$ and $j=1$, and let $\gamma$ be the vector supported on $\{i,j\}$. The coordinate-set/vector correspondence gives $\operatorname{supp}(\gamma)=\{i,j\}$; since $i\ne j$, this support has size $2$. In particular, $\gamma$ is nonzero. To see that $\gamma$ is perpendicular to the constant-pair subspace, use the criterion that membership in a perpendicular subspace is equivalent to having zero dot product with every vector in the original subspace (\texttt{mem_perpendicularSubspace_iff}). That subspace contains only $0$ and the all-ones vector: the dot product with $0$ vanishes, and the dot product with the all-ones vector is the sum of the two supported coordinates, which is $1+1=0$ in $\mathbb F_2$. The dot-product/support identity (\texttt{f₂DotProduct_eq_coordinateSum_f₂Support}) makes this last computation explicit. The density of a subspace is its perpendicular subspace's character sum (\texttt{subsetDensity_submodule_fourier_expansion}); a vector in that perpendicular subspace has Fourier coefficient $1$ in this character sum (\texttt{vectorFourierCoeff_subspaceCharacterSum_of_mem}). Applying these facts to $\gamma$ proves the coefficient assertion.

**Key facts.** `FABL.f₂DotProduct_eq_coordinateSum_f₂Support`, `FABL.mem_perpendicularSubspace_iff`, `FABL.subsetDensity_submodule_fourier_expansion`, `FABL.vectorFourierCoeff_subspaceCharacterSum_of_mem`.
