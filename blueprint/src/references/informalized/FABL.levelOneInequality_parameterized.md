<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter09/HypercontractiveApplications.lean :: FABL.levelOneInequality_parameterized -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Level-one Fourier weight bound

**Claim.** For a Boolean-valued function of mean $\alpha$ and $0<\rho\leq 1$, its level-one Fourier weight is at most $\rho^{-1}(\alpha^{2/(1+\rho)}-\alpha^2)$.

**Proof.** The level-one spectral estimate bounds $\rho$ times the level-one Fourier weight by the noise stability at parameter $\rho$ minus the square of the mean (`rho_mul_fourierWeightAtLevel_one_le_stability_sub_mean_sq`). The small-set expansion estimate bounds that noise stability above by $\alpha^{2/(1+\rho)}$ for a function taking values $0$ and $1$ (`smallSetExpansion`). Substituting the given mean into the spectral estimate and combining these inequalities gives $\rho W_1[f]\leq \alpha^{2/(1+\rho)}-\alpha^2$. Since $\rho>0$, divide by $\rho$ to obtain the claim.

**Key facts.** `FABL.rho_mul_fourierWeightAtLevel_one_le_stability_sub_mean_sq`, `FABL.smallSetExpansion`.
