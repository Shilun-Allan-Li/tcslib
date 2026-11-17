<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter06/LearningAndTesting/DeterministicGoldreichLevin.lean :: FABL.DeterministicGoldreichLevinInput.restrictedWeightAlgorithmScale_add_one_cast_le_runtimeScale -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Restricted weight scale bound

**Claim.** The sum of the inner and outer small-bias scales, plus one, is at most $2^{16}R^{11}$.

**Proof.** 1. Set $R$ equal to the runtime scale, and write $\varepsilon$ for the learning accuracy, $n$ for the dimension, $s$ for the Fourier bound, and $M$ for the family-size bound. The runtime-scale factor bounds give $R\ge1$, $n\le R$, $s\le R$, and $1/\varepsilon\le R$ (`runtimeScale_factor_bounds`). The family-size estimate gives $M\le6R^3$ (`familySizeBound_add_one_cast_le_runtimeScale`), and positivity of $M$ is available from `familySizeBound_pos`.

2. For each of the inner and outer generator inputs, its scale plus one is bounded by its dimension divided by its accuracy, plus two (`smallBiasInput_scale_cast_le_dimension_div_epsilon_add_one`). The generator accuracy is the restricted-weight accuracy divided by its Fourier bound (`generatorInput_epsilon`). For the inner input, the bias parameter relation (`innerInput_biasParameter`), together with the restricted-weight accuracy $\tau^2/8$ (`restrictedWeightInput_epsilon`) and the threshold identity $\tau=\varepsilon/(4M)$ (`threshold_cast`), makes this scale bound at most $512nsM^2/\varepsilon^2+2$. Substituting $n,s\le R$, $M\le6R^3$, and $1/\varepsilon\le R$ yields $18432R^{10}+2\le2^{15}R^{10}$, using $R\ge1$.

3. For the outer input, its Fourier bound is squared, so its generator accuracy has the corresponding squared Fourier factor (`outerInput_biasParameter`, along with `generatorInput_epsilon`). The same scale estimate now gives at most $512ns^2M^2/\varepsilon^2+2$, which is bounded by $18432R^{11}+2\le2^{15}R^{11}$.

4. The algorithm scale is the sum of these two scales. Since $R\ge1$, the inner estimate also implies an upper bound $2^{15}R^{11}$. Adding the two scale-plus-one bounds gives at most $2^{16}R^{11}$, which also bounds the sum of the scales plus one.

**Key facts.** `FABL.DeterministicGoldreichLevinInput.runtimeScale_factor_bounds`, `FABL.DeterministicGoldreichLevinInput.familySizeBound_add_one_cast_le_runtimeScale`, `FABL.DeterministicGoldreichLevinInput.familySizeBound_pos`, `FABL.DeterministicGoldreichLevinInput.restrictedWeightInput_epsilon`, `FABL.DeterministicGoldreichLevinInput.threshold_cast`, `FABL.RestrictedWeightInput.innerInput_biasParameter`, `FABL.SmallBiasFourierInput.generatorInput_epsilon`, `FABL.smallBiasInput_scale_cast_le_dimension_div_epsilon_add_one`, `FABL.RestrictedWeightInput.outerInput_biasParameter`.
