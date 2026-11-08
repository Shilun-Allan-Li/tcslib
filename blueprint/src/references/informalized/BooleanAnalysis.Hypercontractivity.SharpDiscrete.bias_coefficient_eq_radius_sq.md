<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/Hypercontractivity/RandomVariables/Sharp/Parameters.lean :: BooleanAnalysis.Hypercontractivity.SharpDiscrete.bias_coefficient_eq_radius_sq -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Bias coefficient and squared radius

**Claim.** If $1<p<2$, $0<\alpha<\beta$, and $\alpha^p+\beta^p=1$, then the bias coefficient equals $\rho(p/(p-1),\alpha^p)^2$.

**Proof.** The normalization gives $1-\alpha^p=\beta^p$, so the log-odds in the radius formula simplify to $\log(\beta^p/\alpha^p)=p\log(\beta/\alpha)$. Also, direct algebra gives $\bigl(p/(p-1)\bigr)/\bigl(p/(p-1)-1\bigr)=p$. Consequently, the two hyperbolic-sine arguments in the square of the radius reduce to $(p-1)\log(\beta/\alpha)$ and $\log(\beta/\alpha)$. The bias coefficient has precisely the ratio of these hyperbolic sines (`bias_coefficient_eq_sinh`). Its positivity (`bias_coefficient_pos_lt_one`) permits squaring the square root in the definition of the radius without a sign ambiguity. Substitution proves the identity.

**Key facts.** `BooleanAnalysis.Hypercontractivity.SharpDiscrete.bias_coefficient_eq_sinh`, `BooleanAnalysis.Hypercontractivity.SharpDiscrete.bias_coefficient_pos_lt_one`.
