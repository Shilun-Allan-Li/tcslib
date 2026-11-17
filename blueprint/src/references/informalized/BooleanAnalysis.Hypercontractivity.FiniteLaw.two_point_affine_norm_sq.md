<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/Hypercontractivity/RandomVariables/FiniteLaw.lean :: BooleanAnalysis.Hypercontractivity.FiniteLaw.two_point_affine_norm_sq -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Two-point affine norm

**Claim.** If a measurable random variable on a probability space takes only the two distinct values $x$ and $y$, with respective masses $\lambda$ and $1-\lambda$, then the squared norm of its affine transform is the stated weighted two-point absolute moment raised to the power $2/q$.

**Proof.** The assumed masses add to one: since $0\le\lambda\le1$, their extended-real representations add to the representation of $1$. The two-point support result (`BooleanAnalysis.Hypercontractivity.FiniteLaw.ae_two_point_of_mass_sum`) then shows that $X=x$ or $X=y$ almost everywhere. Apply the finite-law affine norm formula (`BooleanAnalysis.Hypercontractivity.FiniteLaw.finite_law_affine_norm_sq`) to the finite set $\{x,y\}$. Because $x\ne y$, its two elements are distinct, so the resulting finite sum has exactly the two terms corresponding to these values. Substituting the given masses and converting their nonnegative real representations to real numbers gives the claimed expression.

**Key facts.** `BooleanAnalysis.Hypercontractivity.FiniteLaw.ae_two_point_of_mass_sum`, `BooleanAnalysis.Hypercontractivity.FiniteLaw.finite_law_affine_norm_sq`.
