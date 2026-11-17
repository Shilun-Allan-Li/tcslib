<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/LearningTheory/Hedge/Hoeffding.lean :: hoeffding_log_mgf_weak -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Weak Hoeffding log-MGF bound

**Claim.** For a probability vector and losses in $[0,1]$, the logarithm of the weighted exponential loss is at most $-\eta L+\eta^2/2$, where $L$ is the average loss.

**Proof.** Set $L=\sum_i p_i\ell_i$. The weighted affine bound gives $\sum_i p_i e^{-\eta\ell_i}\le 1-(1-e^{-\eta})L$, and the assumptions on the weights and losses give $0\le L\le1$. The sum inside the logarithm is positive because some weight is positive and every exponential is positive. By monotonicity of logarithm, it suffices to bound the logarithm of the affine expression. Write that expression as $1+u$, where $u=-(1-e^{-\eta})L$. Since $e^{-\eta}<1$ and $L\le1$, we have $u>-1$, so $\log(1+u)\le u$. Finally, $\eta-1+e^{-\eta}\le\eta^2/2$; multiplying by $L\in[0,1]$ and rearranging gives $-(1-e^{-\eta})L\le -\eta L+\eta^2/2$. Combining these inequalities proves the claim.

**Key facts.** `weighted_exp_le_affine`, `log_one_add_le`, `eta_exp_bound`.
