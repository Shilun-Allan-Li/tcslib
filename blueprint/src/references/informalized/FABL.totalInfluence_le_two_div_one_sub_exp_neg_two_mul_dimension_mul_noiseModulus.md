<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter05/PolynomialThresholdUniformStability.lean :: FABL.totalInfluence_le_two_div_one_sub_exp_neg_two_mul_dimension_mul_noiseModulus -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Influence Bound from Noise Sensitivity

**Claim.** Under the stated uniform noise-sensitivity bound for polynomial threshold functions of degree at most $k$, the total influence of $f$ is at most $\frac{2n}{1-e^{-2}}$ times the bound evaluated at noise parameter $1/n$.

**Proof.** Choose the half-noise parameter $\delta=1/n$, which lies in $[0,1/2]$ because $n\ge2$. The hypothesis applied to $f$ bounds its noise sensitivity at this parameter by $\varepsilon(1/n)$. The inverse-dimension noise-sensitivity estimate then bounds total influence by $\frac{2n}{1-e^{-2}}$ times that noise sensitivity (`FABL.totalInfluence_le_constant_mul_dimension_of_noiseSensitivity_inverseDimension_le`). Substitution of the assumed bound gives the result.

**Key facts.** `FABL.totalInfluence_le_constant_mul_dimension_of_noiseSensitivity_inverseDimension_le`.
