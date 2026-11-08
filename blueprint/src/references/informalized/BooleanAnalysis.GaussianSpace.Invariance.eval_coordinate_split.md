<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/GaussianSpace/Invariance/Coordinates.lean :: BooleanAnalysis.GaussianSpace.Invariance.eval_coordinate_split -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Coordinate decomposition of evaluation

**Claim.** For a multilinear polynomial, evaluation at the family of inputs splits into the contribution from sets omitting coordinate $i$ and the contribution from sets containing $i$, which is $X_i(\omega)$ times the evaluation of the coordinate derivative polynomial.

**Proof.** The evaluation of the coordinate-free polynomial is the sum over subsets $T$ that omit $i$ of $F(T)\prod_{j\in T}X_j(\omega)$ (coordinateFree_eval_sum). The evaluation of the coordinate derivative is the corresponding sum of $F(T\cup\{i\})\prod_{j\in T}X_j(\omega)$ (coordinateDerivative_eval_sum). Every subset of the full coordinate set either omits $i$, or is uniquely $T\cup\{i\}$ for a subset $T$ omitting $i$. Splitting the full evaluation into these two classes, each term in the second class factors as $X_i(\omega)$ times its remaining product. Thus the full sum is the coordinate-free evaluation plus $X_i(\omega)$ times the derivative evaluation, by the multilinear sum decomposition (multilinear_sum_insert).

**Key facts.** `BooleanAnalysis.GaussianSpace.Invariance.coordinateFree_eval_sum`, `BooleanAnalysis.GaussianSpace.Invariance.coordinateDerivative_eval_sum`, `BooleanAnalysis.Hypercontractivity.multilinear_sum_insert`.
