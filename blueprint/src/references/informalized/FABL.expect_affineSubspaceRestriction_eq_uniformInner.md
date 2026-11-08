<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter03/Restrictions.lean :: FABL.expect_affineSubspaceRestriction_eq_uniformInner -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Affine restriction and uniform inner product

**Claim.** The uniform average of $f(h+z)$ over $h\in H$ equals the uniform inner product of the density of $H$ with the translate $x\mapsto f(x+z)$.

**Proof.** Express the average of the affine restriction over $H$ as a sum of Fourier contributions indexed by the perpendicular subspace (`expect_affineSubspaceRestriction_eq_sum`). The uniform inner product of the density of $H$ with the translated function has the same Fourier-sum expression (`uniformInner_subsetDensity_domainTranslate_eq_sum`). Since both sides equal that sum, they are equal.

**Key facts.** `FABL.expect_affineSubspaceRestriction_eq_sum`, `FABL.uniformInner_subsetDensity_domainTranslate_eq_sum`.
