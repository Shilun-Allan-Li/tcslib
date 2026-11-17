<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/Hypercontractivity/Cube/Reverse/TwoPoint.lean :: BooleanAnalysis.Hypercontractivity.choose_even_ratio_step -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Successor comparison for even binomial coefficients

**Claim.** If the even generalized binomial coefficient comparison holds at $2K$, then it holds at $2(K+1)$ under the stated assumptions.

**Proof.** The recurrence for successive even generalized binomial coefficients expresses the coefficient at $2(K+1)$ as the coefficient at $2K$, multiplied by $(p-2K)(p-(2K+1))/((2K+1)(2K+2))$, and similarly for $q$ (\texttt{ring\_choose\_even\_succ}). The factor estimate needed to compare these expressions comes from applying the Borell factor bound at $m=2K$ and $m=2K+1$ (\texttt{borell\_factor\_bound}) and multiplying the resulting inequalities. In detail, it gives $\rho^2(2K-q)(2K+1-q)\le(2K-p)(2K+1-p)$. The comparison term $(p/q)\binom q{2K}\rho^{2K}$ is nonpositive, since $p/q>0$, $\rho^{2K}\ge0$, and even generalized binomial coefficients of $q\in(0,1)$ are nonpositive (\texttt{ring\_choose\_even\_nonpos}). Thus multiplying the factor estimate by that term reverses its inequality direction. Combining this with the induction hypothesis yields the required comparison of the recurrence numerators, including the factor $\rho^2$ that changes $\rho^{2K}$ to $\rho^{2(K+1)}$. The common denominator $(2K+1)(2K+2)$ is positive, so division preserves the inequality and proves the successor claim.

**Key facts.** `BooleanAnalysis.Hypercontractivity.borell_factor_bound`, `BooleanAnalysis.Hypercontractivity.ring_choose_even_nonpos`, `BooleanAnalysis.Hypercontractivity.ring_choose_even_succ`.
