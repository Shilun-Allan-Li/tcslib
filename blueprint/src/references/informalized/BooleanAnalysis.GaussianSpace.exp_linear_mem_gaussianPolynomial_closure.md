<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/GaussianSpace/Noise/PolynomialApproximation.lean :: BooleanAnalysis.GaussianSpace.exp_linear_mem_gaussianPolynomial_closure -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Exponential in the Gaussian polynomial closure

**Claim.** If a complex $L^p$ function agrees almost everywhere with the exponential of a continuous real-linear map, then it belongs to the $L^p$ closure of the functions represented by complex polynomials.

**Proof.** First represent the linear map $L$ on real inputs by a complex polynomial $Q$ (\texttt{exists_polynomial_eval_linear}). For each integer $k\ge 0$, form the polynomial $P_k=\sum_{m<k}Q^m/m!$. Its value at $x$ is the degree-$k$ partial sum $\sum_{m<k}(L(x))^m/m!$ of the exponential series. Each polynomial evaluation defines an $L^p$ function: polynomial evaluations have finite $p$-moment under Gaussian measure when $p<\infty$ (\texttt{memLp_eval_gaussian}). The given function agrees almost everywhere with $e^{L(x)}$, so the $L^p$ distance from the class represented by $P_k$ to $f$ equals the $L^p$ norm of the pointwise Taylor remainder; the equality follows from the almost-everywhere identifications of these representatives. The Gaussian Taylor convergence theorem says these remainder norms tend to zero (\texttt{tendsto_gaussian_exp_taylor}). Thus the polynomial classes converge to $f$ in $L^p$. Since every term is in the range of the polynomial-to-$L^p$ map, the limit belongs to the closure of that range.

**Key facts.** `BooleanAnalysis.GaussianSpace.exists_polynomial_eval_linear`, `BooleanAnalysis.GaussianSpace.memLp_eval_gaussian`, `BooleanAnalysis.GaussianSpace.tendsto_gaussian_exp_taylor`.
