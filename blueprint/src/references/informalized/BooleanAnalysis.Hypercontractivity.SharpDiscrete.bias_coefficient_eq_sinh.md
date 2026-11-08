<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/Hypercontractivity/RandomVariables/Sharp/Parameters.lean :: BooleanAnalysis.Hypercontractivity.SharpDiscrete.bias_coefficient_eq_sinh -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Hyperbolic formula for the bias coefficient

**Claim.** For $0<\alpha<\beta$, the bias coefficient is $\sinh((p-1)\log(\beta/\alpha))/\sinh(\log(\beta/\alpha))$.

**Proof.** Set $t=\beta/\alpha$. The hypotheses imply $t>1$, so $\sinh(\log t)>0$. They also imply $\alpha^2-\beta^2\ne0$, and both $\alpha^p$ and $\beta^p$ are positive. It is therefore enough to verify the claimed equality after cross-multiplying its denominators. Rewrite $\exp((p-1)\log t)$ as $t^{p-1}$ and expand the hyperbolic sines as differences of exponentials. The real-power laws then express the resulting terms using powers of $\alpha$ and $\beta$; clearing the nonzero factors reduces the identity to algebraic equality. This establishes the formula.
