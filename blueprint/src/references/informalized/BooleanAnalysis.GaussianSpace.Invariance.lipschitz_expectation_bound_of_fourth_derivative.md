<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/GaussianSpace/Invariance/Smoothing.lean :: BooleanAnalysis.GaussianSpace.Invariance.lipschitz_expectation_bound_of_fourth_derivative -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Lipschitz Expectation Bound from Fourth Derivatives

**Claim.** Under the stated fourth-derivative comparison hypothesis, the expectations of a $c$-Lipschitz function of $U$ and $V$ differ by at most $16cB^{1/4}$.

**Proof.** If $B>0$, set $\eta=B^{1/4}$ in the scale-dependent estimate (\texttt{lipschitz_expectation_bound_at_scale}). Then $\eta^4=B$, so the two terms in that estimate agree: $8c\eta+(8c/\eta^3)B=16c\eta=16cB^{1/4}$. If $B=0$, the scale-dependent estimate gives a bound of $8c\eta$ for every $\eta>0$. Given any $\delta>0$, choose $\eta=\delta/(8c+1)$; then $8c\eta<\delta$. Thus the nonnegative absolute difference is at most every positive $\delta$, and hence is zero, as required.

**Key facts.** `BooleanAnalysis.GaussianSpace.Invariance.lipschitz_expectation_bound_at_scale`.
