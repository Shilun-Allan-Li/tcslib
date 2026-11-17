<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter04/Tribes.lean :: FABL.fourierCoeff_andFunction_empty -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Empty Coefficient of Conjunction

**Claim.** The empty-set Fourier coefficient of the conjunction function is $1-2\cdot 2^{-w}$.

**Proof.** The empty-set coefficient equals the mean of the function (FABL.mean_eq_fourierCoeff_empty). The mean of a sign-valued function is the probability of output $1$ minus the probability of output $-1$ (FABL.mean_booleanFunction_eq_prob_one_sub_prob_neg_one). The conjunction outputs $-1$ at exactly the all-$-1$ input, whose uniform probability is $2^{-w}$ (FABL.uniformProbability_andFunction_eq_neg_one). Its two output probabilities sum to one (FABL.uniformProbability_one_add_neg_one_eq_one), so the probability of output $1$ is $1-2^{-w}$. Subtracting $2^{-w}$ from this gives $1-2\cdot 2^{-w}$.

**Key facts.** `FABL.mean_booleanFunction_eq_prob_one_sub_prob_neg_one`, `FABL.uniformProbability_andFunction_eq_neg_one`, `FABL.uniformProbability_one_add_neg_one_eq_one`, `FABL.mean_eq_fourierCoeff_empty`.
