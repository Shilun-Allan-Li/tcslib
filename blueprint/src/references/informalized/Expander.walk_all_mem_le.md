<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/Expanders/Walks.lean :: Expander.walk_all_mem_le -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Probability of Walks Contained in a Set

**Claim.** If $B$ occupies at most a fraction $\beta$ of the state space and the operator norm on vectors orthogonal to the uniform vector is at most $\lambda$, then the probability that every state in a length-$k$ walk lies in $B$ is at most $((1-\lambda)\sqrt{\beta}+\lambda)^k$.

**Proof.** First, if $\beta\ge 1$, then $\sqrt{\beta}\ge 1$. Since $0\le\lambda\le1$, the base $(1-\lambda)\sqrt{\beta}+\lambda$ is at least $1$. Its $k$th power is consequently at least $1$, while the probability of any event is at most $1$, proving the bound in this case.

Now suppose $\beta<1$. Group the walks whose states all lie in $B$ according to their final state. The endpoint-distribution identity for restricted walks (`Expander.walk_filter_sum`) identifies each group’s total probability with the corresponding coordinate of the restricted-walk vector. Converting the finite probability sum to a real sum, nonnegativity of those coordinates (`Expander.resVec_nonneg`) permits this identification term by term. The total probability is thus the sum of the coordinates of that vector.

By the sum-versus-Euclidean-norm bound (`Expander.sum_le_sqrt_mul_norm`), this sum is at most $\sqrt n$ times the vector’s norm. The norm estimate for restricted-walk vectors (`Expander.norm_resVec_le`) bounds that norm by the claimed base to the power $k$ times the initial vector’s norm. The initial-vector estimate (`Expander.norm_resVec_zero_le`) bounds the latter by $\sqrt{\beta}/\sqrt n$. Since $\sqrt{\beta}\le1$, multiplication by $\sqrt n$ cancels the denominator and leaves at most the claimed $k$th power. This proves the real-valued probability bound, and applying the increasing map $x\mapsto\operatorname{ENNReal.ofReal}(x)$ gives the stated extended-real inequality.

**Key facts.** `Expander.walk_filter_sum`, `Expander.resVec_nonneg`, `Expander.sum_le_sqrt_mul_norm`, `Expander.norm_resVec_le`, `Expander.norm_resVec_zero_le`.
