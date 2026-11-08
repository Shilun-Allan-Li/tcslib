<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/GaussianSpace/Invariance/Coordinates.lean :: BooleanAnalysis.GaussianSpace.Invariance.coordinateDerivative_eval -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Evaluation of the derivative polynomial

**Claim.** At every Boolean-cube input, evaluating the coefficient family formed from the Fourier coefficients of the Boolean-cube derivative of $F$ in the Walsh basis gives that discrete derivative.

**Proof.** Fix an input $x$. The Walsh expansion theorem expresses the derivative of the Boolean-cube function at $x$ as the sum, over all subsets $S$, of its Fourier coefficient at $S$ times the Walsh character indexed by $S$ at $x$. By definition, these Fourier coefficients are precisely the coefficients of the coordinate derivative polynomial. Its Walsh-basis evaluation at $x$ is therefore the same sum, proving the equality at every input.

**Key facts.** `BooleanAnalysis.walsh_expansion`.
