<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter02/NoiseStability/FourierFormulas.lean :: FABL.noiseSensitivity_le_delta_mul_totalInfluence -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Noise Sensitivity Bound by Total Influence

**Claim.** For a Boolean function and noise rate $\delta\in[0,1]$, its noise sensitivity is at most $\delta$ times its total influence.

**Proof.** For each Fourier level $k$, Bernoulli’s inequality gives $(1-2\delta)^k\ge 1-2\delta k$, since $-2\delta\ge-2$. Rearranging yields $1-(1-2\delta)^k\le2\delta k$. Express noise sensitivity as the level sum with weights $\tfrac12(1-(1-2\delta)^k)$ (`noiseSensitivity_eq_sum_level`), and express total influence as the corresponding sum weighted by $k$ (`totalInfluence_eq_sum_level_mul_fourierWeight`). Each level’s Fourier weight is nonnegative, so the coefficient inequality can be multiplied by that weight and summed. The resulting bound is exactly noise sensitivity at most $\delta$ times total influence.

**Key facts.** `FABL.noiseSensitivity_eq_sum_level`, `FABL.totalInfluence_eq_sum_level_mul_fourierWeight`.
