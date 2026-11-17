<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter06/F₂Polynomials/SiegenthalerSharpness.lean :: FABL.f₂CubeOfFinset_not_mem_perpendicular_constantPairSubspace_of_card_one -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# A Singleton Indicator Is Not Orthogonal to Constants

**Claim.** If a finite set $T\subseteq\mathrm{Fin}(n)$ has cardinality one, its binary indicator vector is not orthogonal, under the coordinate dot product over $\mathbb{F}_2$, to the subspace consisting of zero and the all-ones vector.

**Proof.** Orthogonality to the constant-pair subspace would require the dot product with every vector in that subspace to be zero (the membership criterion for the perpendicular subspace, `FABL.mem_perpendicularSubspace_iff`). Choose the all-ones vector, which belongs to the subspace by the characterization `FABL.mem_constantPairSubspace_iff`. The dot product of the indicator vector with this vector equals the coordinate sum over its support (`FABL.f₂DotProduct_eq_coordinateSum_f₂Support`). The support is exactly $T$, by the inverse property of the indicator/support correspondence. Since $T$ has one element, write $T=\{i\}$; the sum is then the single coordinate of the all-ones vector, namely $1$. This is nonzero in $\mathbb{F}_2$, so the required orthogonality fails.

**Key facts.** `FABL.mem_perpendicularSubspace_iff`, `FABL.mem_constantPairSubspace_iff`, `FABL.f₂DotProduct_eq_coordinateSum_f₂Support`.
