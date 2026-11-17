<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter09/HypercontractiveApplications.lean :: FABL.levelOneInequality_sharp -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Sharp level-one inequality

**Claim.** For a Boolean-valued function of mean $\alpha$, the level-one Fourier weight is at most $2\alpha^2\ln(1/\alpha)$.

**Proof.** First, averaging the pointwise bounds $0\leq f\leq1$ gives $0\leq\alpha\leq1$. If $\alpha=0$, the zero-mean result says the level-one weight is zero (`sharpLevelOneInequality_eq_zero`), yielding the bound. Otherwise $\alpha>0$. When $\alpha\leq1/2$, apply the sharp level-one inequality directly (`sharpLevelOneInequality`). For $\alpha>1/2$, Boolean values give $\mathbb E[f^2]=\alpha$. The variance identity expressing variance as the second moment minus the square of the mean then gives $\operatorname{Var}(f)=\alpha(1-\alpha)$ (`variance_eq_sum_sq_fourierCoeff`). The level-one weight is at most the variance (`fourierWeightAtLevel_one_le_variance`). Because $\alpha>1/2$, we have $\alpha(1-\alpha)\leq2\alpha^2(1-\alpha)$. Finally, for $0<\alpha\leq1$, the logarithm inequality $1-\alpha\leq\ln(1/\alpha)$ shows this is at most $2\alpha^2\ln(1/\alpha)$.

**Key facts.** `FABL.sharpLevelOneInequality_eq_zero`, `FABL.sharpLevelOneInequality`, `FABL.variance_eq_sum_sq_fourierCoeff`, `FABL.fourierWeightAtLevel_one_le_variance`.
