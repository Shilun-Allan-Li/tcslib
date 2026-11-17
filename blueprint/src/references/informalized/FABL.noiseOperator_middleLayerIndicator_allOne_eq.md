<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter05/FourierCoefficientsOfMajority.lean :: FABL.noiseOperator_middleLayerIndicator_allOne_eq -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Middle-Layer Noise Probability

**Claim.** At the all-ones input, the noise operator applied to the middle-layer indicator equals $\binom{2m}{m}2^{-2m}(1-\rho^2)^m$.

**Proof.** First use the product-form expression for the value: it is $\binom{2m}{m}\bigl((1+\rho)/2\bigr)^m\bigl((1-\rho)/2\bigr)^m$ (`noiseOperator_middleLayerIndicator_allOne_eq_product`). The two factors inside the powers multiply to $(1-\rho^2)/4$. Raising this identity to the $m$th power and using $4^m=2^{2m}$ yields the stated formula.

**Key facts.** `FABL.noiseOperator_middleLayerIndicator_allOne_eq_product`.
