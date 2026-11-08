<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter05/GaussianIsoperimetricAsymptotics.lean :: FABL.tendsto_standardGaussianUpperQuantile_atBot -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Quantile diverges at zero tail

**Claim.** As $\alpha$ tends to $0$ in the order topology on $(0,1)$, the standard Gaussian upper quantile tends to $+\infty$.

**Proof.** The upper-tail order isomorphism identifies each real number, with the order reversed, with its standard Gaussian upper-tail probability. Its inverse is therefore increasing from $(0,1)$, with its usual order, to the real line with its usual order. As the probability tends to the lower endpoint $0$ in $(0,1)$, the inverse tends to the top of the real line, which is $+\infty$. This is the endpoint-limit property of the inverse order isomorphism.

**Caveat.** The supplied informal_statement describes an asymptotic for a different function and does not match the formal statement or proof. This account follows the formal statement and proof_source.
