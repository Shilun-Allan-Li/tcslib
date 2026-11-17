<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter02/NoiseStability/NoiseKernels.lean :: FABL.pmfExpectation_bind -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Expectation under a mixture

**Claim.** For a finite mixture formed by first sampling $x$ from $P$ and then sampling $y$ from $Q_x$, the expectation of $f(y)$ equals the expectation under $P$ of the conditional expectation under $Q_x$.

**Proof.** Expand the expectation under the bound distribution as a finite sum over $y$. The probability assigned to $y$ by the bound is the sum over $x$ of $P(x)Q_x(y)$. Because all sums are finite, distribute the real-valued sum across this sum of probabilities; converting the nonnegative extended-real products to real products is valid since each probability is finite. Interchange the two finite sums, then factor out $P(x)$ from the inner sum. The result is exactly the expectation over $x$ of the expectation of $f$ under $Q_x$.
