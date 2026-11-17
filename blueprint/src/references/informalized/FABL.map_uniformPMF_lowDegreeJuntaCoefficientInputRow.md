<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter06/LearningAndTesting/LowDegreeJuntaLearning.lean :: FABL.map_uniformPMF_lowDegreeJuntaCoefficientInputRow -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Uniform Coefficient Input Rows

**Claim.** For a fixed frequency set $S$, applying the coefficient-input row extraction to a uniformly chosen batch of restricted assignments gives a uniform batch of sign vectors of the coefficient sample count.

**Proof.** First convert each restricted assignment in the entire batch into its sign-vector representation using the natural coordinatewise equivalence between free assignments and sign vectors. This conversion preserves the uniform distribution, by the fact that an equivalence sends a uniform finite distribution to a uniform finite distribution (`map_uniformPMF_equiv`). The row extraction then amounts to restricting this sign-vector batch to the coefficient sample indices, which are embedded injectively into the restricted batch indices. Projection of a uniform function-valued batch along any such injection is uniform (`map_uniformPMF_injection_projection`). Composing the conversion and projection gives the asserted distribution.

**Key facts.** `FABL.map_uniformPMF_equiv`, `FABL.map_uniformPMF_injection_projection`.
