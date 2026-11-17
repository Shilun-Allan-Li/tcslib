<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter08/DecisionTreeInequalities.lean :: FABL.productProbabilityPMF_permuteInput -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Permutation invariance of a product distribution

**Claim.** Permuting the coordinates of an input tuple does not change its mass under the product distribution with common coordinate law $\pi$.

**Proof.** By the product-mass formula (\texttt{productProbabilityPMF\_apply}), the mass at the permuted tuple is $\prod_{i\in\mathrm{Fin}(n)}\pi(x(\sigma(i)))$. A permutation reindexes the finite set of coordinates bijectively, so this product equals $\prod_{i\in\mathrm{Fin}(n)}\pi(x(i))$, the mass at the original tuple.

**Key facts.** `FABL.productProbabilityPMF_apply`.
