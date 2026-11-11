<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter06/LearningAndTesting/DeterministicGoldreichLevin.lean :: FABL.DeterministicGoldreichLevinInput.activeCap_add_one_cast_le_runtimeScale -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Active Cap Runtime Bound

**Claim.** For a deterministic Goldreich–Levin input, the active cap plus one is at most $2^{13}$ times the eighth power of its runtime scale.

**Proof.** Write $R$ for the runtime scale, $\epsilon$ for the learning parameter, and $M$ for the family size bound. The runtime scale controls both $M+1$ and $1/\varepsilon$; the family-size estimate therefore gives $M\le 6R^3$. The active-cap estimate bounds the cap plus one by $9/\tau^2$. Since the threshold is $\tau=\varepsilon/(4M)$, this last bound is $144M^2(1/\varepsilon)^2$. Applying the two runtime-scale bounds yields $144(6R^3)^2R^2=5184R^8\le 2^{13}R^8$, as required.

**Key facts.** `FABL.DeterministicGoldreichLevinInput.runtimeScale_factor_bounds`, `FABL.DeterministicGoldreichLevinInput.familySizeBound_add_one_cast_le_runtimeScale`, `FABL.goldreichLevinActiveCap_add_one_cast_le`, `FABL.DeterministicGoldreichLevinInput.threshold_cast`.
