<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/Hypercontractivity/RandomVariables/Sharp/FiniteNoiseOptimization.lean :: BooleanAnalysis.Hypercontractivity.SharpDiscrete.finite_noise_homogeneity -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Homogeneity of Weighted Forms

**Claim.** Scaling a vector by a real number $t$ multiplies its weighted $p$-moment by $|t|^p$ and its quadratic noise functional by $t^2$.

**Proof.** For the moment, use $|tf_i|=|t||f_i|$ and the multiplicative law for real powers of nonnegative numbers. Factoring the common factor $|t|^p$ out of the finite sum gives $G(tf)=|t|^pG(f)$. For the quadratic functional, $(tf_i)^2=t^2f_i^2$, and linearity of the weighted sum gives $\sum_iw_i(tf_i)=t\sum_iw_if_i$. Squaring the latter contributes another factor $t^2$. Both terms of $F(tf)$ therefore have the common factor $t^2$, proving $F(tf)=t^2F(f)$.
