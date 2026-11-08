<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/GaussianSpace/Invariance/Smoothing.lean :: BooleanAnalysis.GaussianSpace.Invariance.lipschitz_expectation_bound_at_scale -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Lipschitz Expectation Bound at a Scale

**Claim.** Under the stated fourth-derivative comparison hypothesis, the expectations of a $c$-Lipschitz function of $U$ and $V$ differ by at most $8c\eta+8cB/\eta^3$ for every $\eta>0$.

**Proof.** Choose a $C^4$ approximation $\phi$ to $\psi$ with uniform error at most $4c\eta$ and fourth derivative bounded by $8c/\eta^3$; this is the smooth approximation result (\texttt{exists_contDiff_four_approx}). For each probability space, the integral of $\psi-\phi$ therefore has absolute value at most $4c\eta$: integrability of $\phi(U)$ and $\phi(V)$ follows from their fourth-moment hypotheses and the derivative bound (\texttt{integrable_test_of_memLp_four}), while the Lipschitz compositions are integrable. The uniform integral estimate (\texttt{abs_integral_sub_le_uniform}) gives these two error bounds. Insert the intermediate expectations of $\phi(U)$ and $\phi(V)$ and apply the triangle inequality. The middle difference is at most $(8c/\eta^3)B$ by the assumed smooth-function comparison. Adding the two approximation errors gives the claimed bound.

**Key facts.** `BooleanAnalysis.GaussianSpace.Invariance.exists_contDiff_four_approx`, `BooleanAnalysis.GaussianSpace.integrable_test_of_memLp_four`, `BooleanAnalysis.GaussianSpace.Invariance.abs_integral_sub_le_uniform`.
