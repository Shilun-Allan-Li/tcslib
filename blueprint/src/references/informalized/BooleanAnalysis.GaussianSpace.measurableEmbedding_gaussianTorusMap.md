<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/GaussianSpace/Noise/Torus.lean :: BooleanAnalysis.GaussianSpace.measurableEmbedding_gaussianTorusMap -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Measurable Embedding into the Torus

**Claim.** The map sending each vector to its specified torus coordinates is a measurable embedding.

**Proof.** The map is continuous, and it is injective. A continuous injective map into the torus is a measurable embedding by the continuous-injective-map criterion for measurable embeddings. Thus the two stated properties together give the result.

**Key facts.** `BooleanAnalysis.GaussianSpace.continuous_gaussianTorusMap`, `BooleanAnalysis.GaussianSpace.gaussianTorusMap_injective`.
