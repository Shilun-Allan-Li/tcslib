<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/LearningTheory/JohnsonLindenstrauss/ChiSquaredMGF.lean :: centered_chi_squared_step -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Centered Gaussian Square MGF Bound

**Claim.** If $Y$ has the centered Gaussian law with variance $1/k$ and $|t|\le k/4$, then the exponential of $t(Y^2-1/k)$ is integrable and its moment generating function is at most $\exp(2t^2/k^2)$.

**Proof.** Write $v=1/k$. The assumptions imply $v>0$ and $2tv<1$, so the Gaussian quadratic integral is finite. The Gaussian quadratic integrability formula (\texttt{integrable\_exp\_mul\_sq\_gaussianReal\_zero}) gives integrability of $y\mapsto e^{ty^2}$; the law assumption transfers this integrability to $Y$, and multiplication by the constant $e^{-t/k}$ gives integrability of the centered exponential. The corresponding Gaussian integral formula (\texttt{integral\_exp\_mul\_sq\_gaussianReal\_zero}) evaluates its MGF as $e^{-t/k}/\sqrt{1-2t/k}$. Put $s=t/k$, so $|s|\le1/4$. Rewriting the reciprocal square root using the logarithm expresses this MGF as $\exp(-s-\tfrac12\log(1-2s))$. The bound $-s-\tfrac12\log(1-2s)\le2s^2$ (\texttt{neg\_log\_one\_sub\_two\_mul\_le\_two\_sq}) then yields the claimed estimate.

**Key facts.** `integrable_exp_mul_sq_gaussianReal_zero`, `integral_exp_mul_sq_gaussianReal_zero`, `neg_log_one_sub_two_mul_le_two_sq`.
