<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter08/GeneralizedFourierFormulas.lean :: FABL.productNoiseStability_uniformSign_eq_noiseStability -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Uniform-Sign Noise Stability Identity

**Claim.** On the uniform sign cube, product noise stability at parameter $\rho$ equals the correlated-sign noise stability at the corresponding parameter.

**Proof.** Rewrite product noise stability as the product inner product of $f$ with its image under the product noise operator. On the uniform sign cube, that operator agrees with the sign-cube noise operator (FABL.productNoiseOperator_uniformSign_eq_noiseOperator), and the product inner product agrees with the uniform sign inner product (FABL.productInner_uniformSign). The resulting uniform inner product is the correlated-sign noise stability by the identity FABL.noiseStability_eq_uniformInner_noiseOperator. Together these equalities give the claimed formula.

**Key facts.** `FABL.productNoiseOperator_uniformSign_eq_noiseOperator`, `FABL.productInner_uniformSign`, `FABL.noiseStability_eq_uniformInner_noiseOperator`.
