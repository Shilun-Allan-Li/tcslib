<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/GaussianSpace/Noise/Polynomial.lean :: BooleanAnalysis.GaussianSpace.memLp_eval_gaussian -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Polynomial evaluation is Gaussian-integrable

**Claim.** For a polynomial in finitely many variables with real or complex coefficients and any finite exponent $p$, its evaluation on coordinatewise images of a standard Gaussian vector belongs to $L^p$ for the product standard Gaussian measure.

**Proof.** Induct on the polynomial using the constant, addition, and multiplication-by-a-variable cases. A constant polynomial is in every finite-exponent $L^p$ space. If two polynomial evaluations belong to $L^p$, their sum does too. For multiplication by the variable $x_i$, use Hölder's inequality with both factors in $L^{2p}$ and conjugate-product exponents satisfying $1/(2p)+1/(2p)=1/p$. The coordinate function $x\mapsto x_i$ has every finite Gaussian moment, so it belongs to $L^{2p}$; the induction hypothesis puts the other factor in $L^{2p}$ as well. Their product is therefore in $L^p$.
