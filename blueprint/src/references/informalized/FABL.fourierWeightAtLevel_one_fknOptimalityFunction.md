<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter05/FKNOptimality.lean :: FABL.fourierWeightAtLevel_one_fknOptimalityFunction -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Fourier weight of the optimality function

**Claim.** The level-one Fourier weight of the optimality function is $(1-\mathbb{E}A_q)^2+W_1(A_q)$.

**Proof.** Express the level-one weight as a sum over singleton coordinates. Separate the first coordinate from the remaining coordinates. The first-coordinate coefficient is $1-\delta_q/2$, where $\delta_q=2\mathbb{E}A_q$ (`fourierCoeff_fknOptimalityFunction_zero`), hence it is $1-\mathbb{E}A_q$. Each remaining singleton coefficient agrees with the corresponding coefficient of $A_q$ (`fourierCoeff_fknOptimalityFunction_succ`). Their squares sum to $W_1(A_q)$ by the singleton-sum identity (`fourierWeightAtLevel_one_eq_sum_singleton`). Combining the first square and this remaining sum proves the formula.

**Key facts.** `FABL.fourierWeightAtLevel_one_eq_sum_singleton`, `FABL.fourierCoeff_fknOptimalityFunction_zero`, `FABL.fourierCoeff_fknOptimalityFunction_succ`.
