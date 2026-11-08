<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter08/ProductLTFNoiseCorrection.lean :: FABL.productRetentionPairPMF_apply -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Joint product-pair mass

**Claim.** For sequences $x,y\in\Omega^n$, their joint mass under the retention-and-resampling experiment equals the product-distribution mass of $x$ times the product-noise-kernel mass of $y$ given $x$.

**Proof.** Expand the bind and map defining the joint experiment into finite sums. For the specified pair $(x,y)$, the map vanishes except at starting sequence $x$ and generated sequence $y$. The outer sum therefore contributes only the mass of $x$ under the product distribution, and the inner sum contributes only the conditional mass of $y$ under the product noise kernel. Multiplying these two contributions gives the stated formula.
