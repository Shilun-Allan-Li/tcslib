<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/LearningTheory/Hedge/Hoeffding.lean :: hoeffding_log_mgf_tight -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Tight Hoeffding log-MGF bound

**Claim.** For a probability vector and losses in $[0,1]$, the logarithm of the weighted exponential loss is at most $-$ times the average loss plus $^2/8$.

**Proof.** Let $L=\sum_i p_i\ell_i$. The weighted affine bound for the exponential gives $\sum_i p_i e^{-\eta\ell_i}\le 1-(1-e^{-\eta})L$. The sum on the left is positive: since the weights are nonnegative and sum to one, at least one weight is positive, and its contribution to the sum is positive. Thus monotonicity of the logarithm lets us bound its logarithm by the logarithm of the affine upper bound. The weighted affine bound also gives $0\le L\le1$. Apply the tight Bernoulli log-MGF estimate to this $L$ to obtain $\log(1-L+Le^{-\eta})\le -\eta L+\eta^2/8$, which yields the result.

**Key facts.** `weighted_exp_le_affine`, `bernoulli_mgf_bound`.
