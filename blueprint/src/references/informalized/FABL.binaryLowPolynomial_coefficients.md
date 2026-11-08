<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter06/Constructions/ExecutableFiniteFields.lean :: FABL.binaryLowPolynomial_coefficients -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Polynomial from its coefficients

**Claim.** If a polynomial $p$ has natural degree less than $\ell$, then the low polynomial formed from its coefficients in degrees $0$ through $\ell-1$ equals $p$.

**Proof.** Rewrite the sum over indices in $\mathrm{Fin}\,\ell$ as the sum over the natural numbers from $0$ to $\ell-1$. The degree bound allows the standard coefficient expansion of a polynomial as the finite sum of its coefficients times the corresponding powers of $X$. That expansion is precisely the sum defining the low polynomial, so it equals $p$.
