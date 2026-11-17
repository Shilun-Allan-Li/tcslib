<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/Hypercontractivity/RandomVariables/Sharp/Parameters.lean :: BooleanAnalysis.Hypercontractivity.SharpDiscrete.radius_sq_le_balanced -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Comparison with the balanced radius

**Claim.** If $q>2$ and $0<\lambda<1/2$, then $\rho(q,\lambda)^2\le1/(q-1)$.

**Proof.** Set $u=\log((1-\lambda)/\lambda)$, $t=u/(q/(q-1))$, and $a=1/(q-1)$. Here $u,t>0$ and $0<a\le1$, and direct simplification gives $at=u/q$. The radius bound `radius_pos_lt_one` ensures the ratio under the square root is positive, so squaring the defining square root gives $\rho^2=\sinh(at)/\sinh t$. The scaling inequality for the hyperbolic sine (`sinh_scale_le`) gives $\sinh(at)\le a\sinh t$. Since $\sinh t>0$, division yields $\rho^2\le a=1/(q-1)$.

**Key facts.** `BooleanAnalysis.Hypercontractivity.SharpDiscrete.radius_pos_lt_one`, `BooleanAnalysis.Hypercontractivity.SharpDiscrete.sinh_scale_le`.
