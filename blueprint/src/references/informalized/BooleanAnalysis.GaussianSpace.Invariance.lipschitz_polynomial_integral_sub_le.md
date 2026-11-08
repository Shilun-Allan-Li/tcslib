<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/GaussianSpace/Invariance/Perturbation.lean :: BooleanAnalysis.GaussianSpace.Invariance.lipschitz_polynomial_integral_sub_le -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Lipschitz Stability for Multilinear Random Polynomials

**Claim.** For independent, centered, variance-one random variables with finite fourth moments, the expectations of a $c$-Lipschitz function of two multilinear random polynomials differ by at most $c$ times the Boolean-cube $L^2$ norm of the polynomial formed by their coefficient difference.

**Proof.** First, linearity of the finite polynomial sum shows pointwise that the difference of the two random polynomials is the polynomial with coefficient family $F-G$. Each polynomial has a finite fourth moment: this follows from independence, the coordinate fourth-moment assumptions, and the finite sum defining it (\texttt{evalMultilinearRV_memLp}). In particular, both lie in $L^2$, so the Lipschitz integral estimate in $L^2$ (\texttt{lipschitz_integral_sub_le_two_norm}) bounds the difference of expectations by $c$ times the $L^2$ norm of their difference. The independence, centering, and unit second moments identify that random polynomial's $L^2$ norm with the Boolean-cube norm of its coefficient polynomial (\texttt{polynomial_two_norm_eq_l2Norm}). Substituting the coefficient family $F-G$ gives the asserted bound.

**Key facts.** `BooleanAnalysis.Hypercontractivity.evalMultilinearRV_memLp`, `BooleanAnalysis.GaussianSpace.Invariance.lipschitz_integral_sub_le_two_norm`, `BooleanAnalysis.GaussianSpace.Invariance.polynomial_two_norm_eq_l2Norm`.
