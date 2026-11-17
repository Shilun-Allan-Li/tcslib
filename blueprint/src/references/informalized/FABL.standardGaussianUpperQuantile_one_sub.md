<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter05/GaussianIsoperimetric.lean :: FABL.standardGaussianUpperQuantile_one_sub -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Symmetry of Gaussian upper quantiles

**Claim.** For every $0<\alpha<1$, the standard Gaussian upper quantile at $1-\alpha$ is the negative of its value at $\alpha$.

**Proof.** The upper tail at the quantile of any probability in $(0,1)$ returns that probability (\texttt{standardGaussianUpperTail\_quantile}). Therefore the upper tails of the two quantiles in question are $1-\alpha$ and $\alpha$. The upper tail at $-t$ equals one minus the upper tail at $t$ (\texttt{standardGaussianUpperTail\_neg}), so the upper tail of the quantile at $1-\alpha$ also equals the upper tail at the negative of the quantile at $\alpha$. Since the upper-tail function is strictly decreasing, it is injective; the two inputs must be equal.

**Key facts.** `FABL.standardGaussianUpperTail_quantile`, `FABL.standardGaussianUpperTail_neg`, `FABL.standardGaussianUpperTail_strictAnti`.
