<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/GaussianSpace/Invariance/Coordinates.lean :: BooleanAnalysis.GaussianSpace.Invariance.coordinateFree_eval_sum -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Evaluation of the coordinate-free polynomial

**Claim.** For each outcome $\omega$, evaluating the coordinate-free polynomial on the random inputs equals the sum of $F(T)\prod_{j\in T}X_j(\omega)$ over subsets $T$ not containing $i$.

**Proof.** By definition, the coordinate-free polynomial has zero coefficients on sets containing $i$, so it is supported on subsets of $[n]\setminus\{i\}$. The supported-evaluation formula therefore rewrites its evaluation as the sum over subsets of that set. On each such subset $T$, the coefficient is $F(T)$, since $i\notin T$. This is exactly the claimed sum.

**Key facts.** `BooleanAnalysis.Hypercontractivity.MultilinearMoments.eval_supported`.
