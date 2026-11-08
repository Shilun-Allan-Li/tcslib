<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/GaussianSpace/Hermite/Basic.lean :: BooleanAnalysis.GaussianSpace.hermiteFunction_indicator -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Indicator-index Hermite formula

**Claim.** For every natural number $n$, finite set $S\subseteq\{1,\ldots,n\}$, and point $x\in\mathbb R^n$, the Hermite function indexed by the multi-index that is $1$ on $S$ and $0$ elsewhere equals $\prod_{i\in S}x_i$.

**Proof.** Express the Hermite function as the product, over all coordinates, of the evaluations of the corresponding normalized one-variable Hermite polynomials (the product formula, `hermiteFunction_eq_prod`). For coordinates in $S$, the index is $1$, and the normalized Hermite polynomial of degree one is $X$ (`normalizedHermitePolynomial_one`), whose evaluation at $x_i$ is $x_i$. For coordinates outside $S$, the index is $0$, and the normalized polynomial is the constant $1$ (`normalizedHermitePolynomial_zero`), whose evaluation is $1$. Thus the full product reduces to the product of $x_i$ over $S$.

**Key facts.** `BooleanAnalysis.GaussianSpace.hermiteFunction_eq_prod`, `BooleanAnalysis.GaussianSpace.normalizedHermitePolynomial_zero`, `BooleanAnalysis.GaussianSpace.normalizedHermitePolynomial_one`.
