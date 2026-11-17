<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/GaussianSpace/Noise/PolynomialApproximation.lean :: BooleanAnalysis.GaussianSpace.gaussianPolynomialLp_closure_eq_top -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Polynomial range is dense

**Claim.** For finite $p\ge1$, the topological closure of the range of the Gaussian polynomial map into Gaussian $L^p$ is the whole space.

**Proof.** The closure of the range is a closed subspace. By the density theorem for the span of Gaussian torus Fourier functions (\texttt{span\_gaussianTorusFourier\_dense}), it suffices to show that each such Fourier function belongs to this closed subspace. The lemma placing each Gaussian torus Fourier function in the closure of the polynomial range (\texttt{gaussianTorusFourier\_mem\_polynomial\_closure}) supplies exactly this inclusion. Hence the closed subspace contains the dense span, so it is the whole space.

**Key facts.** `BooleanAnalysis.GaussianSpace.span_gaussianTorusFourier_dense`, `BooleanAnalysis.GaussianSpace.gaussianTorusFourier_mem_polynomial_closure`.

**Caveat.** The supplied informal statement describes Gaussian polynomial density in a broader theorem and hypercontractivity, but the formal declaration and proof establish only density of the polynomial range in Gaussian $L^p$.
