<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter09/SmallSetExpansion.lean :: FABL.noiseStability_oneThird_le_uniformLpNorm_fourThird_sq -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Noise Stability Bound at One Third

**Claim.** For every real-valued function $f$ on the Boolean cube, its noise stability at correlation $1/3$ is at most the square of its uniform $L^{4/3}$ norm.

**Proof.** Let $a$ be the noise parameter used in the $(2,4)$ hypercontractive estimate. Its square is $1/3$ (`twoFourNoiseRoot_sq`). The stability inner-product identity expresses stability at $1/3$ as the uniform inner product of $f$ with its noise-operator image at that parameter (`noiseStability_eq_uniformInner_noiseOperator`). By the composition law for noise operators, this inner product is $\langle T_a f,T_a f\rangle_u$. The squared uniform $L^2$ norm equals this inner product (`uniformLpNorm_two_sq_eq_uniformInner`), so the stability is $\|T_a f\|_2^2$. The $(2,4)$ hypercontractive bound (`fourThirdTwoHypercontractivity`) gives $\|T_a f\|_2\le \|f\|_{4/3}$. Both sides are nonnegative, so squaring yields the desired inequality.

**Key facts.** `FABL.twoFourNoiseRoot_sq`, `FABL.noiseStability_eq_uniformInner_noiseOperator`, `FABL.noiseOperator_comp`, `FABL.uniformInner_noiseOperator_left`, `FABL.uniformLpNorm_two_sq_eq_uniformInner`, `FABL.fourThirdTwoHypercontractivity`.
