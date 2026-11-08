<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter03/LearningTheory/SparseSpectrum.lean :: FABL.ker_dualRestrict_ker_eq_span -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Kernel of hyperplane restriction

**Claim.** For a nonzero linear functional $\beta$ on the finite-dimensional vector space $V$ over $\mathbb F_2$, the kernel of restriction of linear functionals to $\ker\beta$ is the one-dimensional span of $\beta$.

**Proof.** A functional restricts to zero on $\ker\beta$ exactly when it annihilates that subspace. The dual-annihilator theorem identifies the annihilator of a subspace with the image of the dual map from its quotient description (`Submodule.dualRestrict_ker_eq_dualAnnihilator`). Applied to $\ker\beta$, this says its annihilator is the range of the dual map associated with $\beta$. The range of that dual map is the span of the single functional $\beta$ (`LinearMap.range_dualMap_eq_dualAnnihilator_ker` and `LinearMap.range_dualMap_dual_eq_span_singleton`). Thus the restriction kernel is precisely $\mathbb F_2\,\beta$.
