<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter08/ProductLpInequalities.lean :: FABL.productLpNorm_nonneg -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Nonnegativity of the Product $L^p$ Quantity

**Claim.** The product $L^p$ quantity $(\mathbb E|f|^p)^{1/p}$ is nonnegative for every real $p$ and every function $f$.

**Proof.** Every value $|f(x)|$ is nonnegative, so its real power with exponent $p$ is nonnegative. The expectation of a pointwise nonnegative function under a probability mass function is nonnegative (`pmfExpectation_nonneg`). The product $L^p$ quantity is a real power of that nonnegative expectation, and real powers preserve nonnegativity.

**Key facts.** `FABL.pmfExpectation_nonneg`.
