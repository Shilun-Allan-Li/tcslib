<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter08/ProductLTFNoiseCorrection.lean :: FABL.literalSelector_after_plus -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Conditional selector law factors by coordinate

**Claim.** For a fixed vector $a$, sampling an independent vector from $\pi^{\otimes n}$ and independent correlated sign pairs, then selecting the two outputs coordinatewise, gives the product over coordinates of the one-coordinate laws with fixed value $a_i$.

**Proof.** First fix the sampled second vector. The coordinatewise map from each sign pair to the two selected values sends the independent product law of sign pairs to the independent product of their coordinatewise image laws; this is the coordinatewise mapping property of independent products (`independentProductPMF_map_coordinates`). Now average over the sampled second vector. Its coordinates are independent with law $\pi$, and at coordinate $i$ the subsequent output law depends only on that coordinate. The binding property for independent products (`independentProductPMF_bind_coordinates`) therefore says that averaging produces the independent product of the one-coordinate laws obtained by first sampling from $\pi$ and then applying the sign-pair selection. These are exactly the laws with fixed value $a_i$.

**Key facts.** `FABL.independentProductPMF_map_coordinates`, `FABL.independentProductPMF_bind_coordinates`.
