<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter05/FKNOptimality.lean :: FABL.fourierWeightAtLevel_one_fknOptimalityFunction_eq_delta -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Optimality weight in terms of mass

**Claim.** The level-one Fourier weight of the optimality function is $1-\delta_q+\delta_q^2/4+W_1(A_q)$, where $\delta_q=2\mathbb{E}A_q$.

**Proof.** Use the formula expressing the level-one weight as $(1-\mathbb{E}A_q)^2+W_1(A_q)$ (`fourierWeightAtLevel_one_fknOptimalityFunction`). Substituting $\mathbb{E}A_q=\delta_q/2$ and expanding the square gives $1-\delta_q+\delta_q^2/4+W_1(A_q)$.

**Key facts.** `FABL.fourierWeightAtLevel_one_fknOptimalityFunction`.
