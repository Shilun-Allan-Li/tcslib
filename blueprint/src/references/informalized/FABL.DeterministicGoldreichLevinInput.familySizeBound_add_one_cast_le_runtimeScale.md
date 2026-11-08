<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter06/LearningAndTesting/DeterministicGoldreichLevin.lean :: FABL.DeterministicGoldreichLevinInput.familySizeBound_add_one_cast_le_runtimeScale -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Family Size Runtime Bound

**Claim.** The family size bound plus one is at most six times the cube of the runtime scale.

**Proof.** The family-size estimate bounds the family size plus one by $6(S+1)^2/\varepsilon$, where $S$ is the Fourier bound and $\varepsilon$ is the learning parameter. The runtime-scale bounds give $S+1\le R$ and $1/\varepsilon\le R$. Consequently, $6(S+1)^2/\varepsilon\le 6R^2R=6R^3$.

**Key facts.** `FABL.DeterministicGoldreichLevinInput.runtimeScale_factor_bounds`, `FABL.fourierOneNormFamilySizeBound_add_one_cast_le`.
