<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter08/ProductLTFNoiseCorrection.lean :: FABL.literalProductSelectorPairPMF_eq_productSelectorPairPMF -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Two constructions of selector pair laws

**Claim.** The law obtained by sampling independent vectors from $\pi^{\otimes n}$ and independent coordinatewise correlated sign pairs equals the product law of the corresponding one-coordinate selector pair distribution.

**Proof.** The lemma `literalProductSelectorCoordinatePMF_eq_product` identifies the coordinate-vector construction—sampling the two vectors and the selector pairs, then selecting outputs—with the independent product of the one-coordinate selector pair laws. Applying the coordinate rearrangement that groups the two outputs at each coordinate turns this equality into the asserted equality of laws on pairs of vectors.

**Key facts.** `FABL.literalProductSelectorCoordinatePMF_eq_product`.
