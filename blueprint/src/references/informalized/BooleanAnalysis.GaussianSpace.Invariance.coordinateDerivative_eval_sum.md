<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/GaussianSpace/Invariance/Coordinates.lean :: BooleanAnalysis.GaussianSpace.Invariance.coordinateDerivative_eval_sum -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Derivative evaluation on random inputs

**Claim.** For each outcome $\omega$, the random-input evaluation of the coordinate derivative polynomial equals the sum of $F(T\cup\{i\})\prod_{j\in T}X_j(\omega)$ over subsets $T$ not containing $i$.

**Proof.** The coefficient formula shows that the coordinate derivative polynomial has zero coefficients on sets containing $i$. Consequently it is supported on subsets of $[n]\setminus\{i\}$. The supported-evaluation formula then restricts its full polynomial sum to subsets of this set. For each such $T$, we have $i\notin T$, so the coefficient formula gives the coefficient $F(T\cup\{i\})$. Substituting these coefficients into the restricted sum gives the claimed expression.

**Key facts.** `BooleanAnalysis.Hypercontractivity.MultilinearMoments.eval_supported`, `BooleanAnalysis.GaussianSpace.Invariance.coordinateDerivative_coeff`.
