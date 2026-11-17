<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/GaussianSpace/Hermite/GeneratingFunction.lean :: BooleanAnalysis.GaussianSpace.normalizedHermite_generating_function -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Generating function for normalized Hermite polynomials

**Claim.** For all real numbers $x$ and $t$, the series whose $j$th term is the value of the normalized Hermite polynomial of degree $j$ at $x$, multiplied by $t^j/\sqrt{j!}$, sums to $\exp(tx-t^2/2)$.

**Proof.** For each $j$, the normalized-series summand equals the corresponding unnormalized Hermite summand: $H_j(x)t^j/\sqrt{j!}=\operatorname{He}_j(x)t^j/j!$ (BooleanAnalysis.GaussianSpace.normalizedHermite_generating_summand). The generating-function identity for the unnormalized Hermite polynomials states that the series of these latter terms sums to $\exp(tx-t^2/2)$ (BooleanAnalysis.GaussianSpace.hermite_generating_function). Replacing each term by its equal normalized form gives the claimed sum.

**Key facts.** `BooleanAnalysis.GaussianSpace.normalizedHermite_generating_summand`, `BooleanAnalysis.GaussianSpace.hermite_generating_function`.
