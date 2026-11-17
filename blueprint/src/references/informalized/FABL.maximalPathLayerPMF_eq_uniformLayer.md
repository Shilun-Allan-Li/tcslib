<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter08/BiasedThresholdComplements.lean :: FABL.maximalPathLayerPMF_eq_uniformLayer -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Uniform distribution on a subset layer

**Claim.** Choosing a uniformly random permutation and taking the elements whose images are less than $k$ produces the uniform distribution on the $k$-element subsets.

**Proof.** The set of possible outputs is exactly the layer of $k$-element subsets: every prefix has cardinality $k$ (`card_maximalPathPrefix`), and the layer is nonempty (`powersetCard_univ_nonempty`). Any subset outside this layer has probability zero, since it cannot be a prefix. Within the layer, any two subsets have equal probability by the equal-cardinality result (`maximalPathLayerPMF_eq_of_card_eq`). A probability distribution supported on a nonempty finite set and constant on that set is uniform there (`pmf_eq_uniformOfFinset_of_constant_on`). Applying this fact identifies the prefix distribution with the uniform distribution on the layer.

**Key facts.** `FABL.card_maximalPathPrefix`, `FABL.powersetCard_univ_nonempty`, `FABL.maximalPathLayerPMF_eq_of_card_eq`, `FABL.pmf_eq_uniformOfFinset_of_constant_on`.
