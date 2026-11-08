<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter03/GoldreichLevin/Estimator.lean :: FABL.runWithCost_restrictedFourierWeightEstimatorProgram_uniformProduct -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Uniform Product Sampling for the Estimator

**Claim.** The estimator's run law is equivalent to drawing one uniform triple of input sequences and applying the estimator output map, with the estimator's specified cost.

**Proof.** First use the estimator run calculation to express the law as three nested uniform draws, each followed by the deterministic estimator output and fixed cost. The uniform triple-product identity (`uniformPMF_bind_bind_map_triple`) identifies those nested draws with one uniform draw from the product of three sequence spaces. Applying the same output-and-cost map to both sides preserves equality of the laws, yielding the claimed expression.

**Key facts.** `FABL.runWithCost_restrictedFourierWeightEstimatorProgram`, `FABL.uniformPMF_bind_bind_map_triple`.
