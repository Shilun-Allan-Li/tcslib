<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter06/LearningAndTesting/DeterministicGoldreichLevin.lean :: FABL.DeterministicGoldreichLevinInput.coefficientGeneratorScale_add_one_cast_le_runtimeScale -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Coefficient Generator Scale Bound

**Claim.** For every deterministic Goldreich–Levin input, the coefficient input's generator scale plus one is at most $2^{15}$ times the eleventh power of the runtime scale.

**Proof.** Write $R$ for the runtime scale, $\varepsilon$ for the learning parameter, $M$ for the family size bound, and $S$ for the Fourier bound. The runtime-scale estimates control the dimension, $S$, and $1/\varepsilon$ by $R$. The active-cap estimate also gives $M\le 2^{13}R^8$. By the generator-accuracy identities, its accuracy is $\varepsilon/(2MS)$. The ceiling-scale estimate then bounds the generator scale plus one by $2nMS/\varepsilon+2$. Substituting the runtime bounds gives at most $2R(2^{13}R^8)R^2+2=2^{14}R^{11}+2$. Since $R\ge1$, this is at most $2^{15}R^{11}$.

**Key facts.** `FABL.DeterministicGoldreichLevinInput.runtimeScale_factor_bounds`, `FABL.DeterministicGoldreichLevinInput.activeCap_add_one_cast_le_runtimeScale`, `FABL.SmallBiasFourierInput.generatorInput_epsilon`, `FABL.DeterministicGoldreichLevinInput.coefficientInput_epsilon`, `FABL.smallBiasInput_scale_cast_le_dimension_div_epsilon_add_one`.
