<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter09/HypercontractiveAnticoncentration.lean :: FABL.translated_anticoncentration_exact -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Exact Translated Anticoncentration

**Claim.** For a mean-zero random variable with positive $L^2$ norm that satisfies the stated hypercontractivity condition, the probability that $|X-\theta|>t\|X\|_2$ is at least the square of the displayed rational expression.

**Proof.** Normalize by setting $L=\|X\|_2$ and $X_n=X/L$. Its mean is zero, its $L^2$ norm is $1$, and constant scaling preserves the hypercontractivity condition (`IsHypercontractiveRandomVariable.const_mul`). Apply the normalized translated anticoncentration theorem to $X_n$, with shift $\theta/L$ (`translated_anticoncentration_normalized`). Since $L>0$, the event $t<|X_n-\theta/L|$ is equivalent pointwise to $tL<|X-\theta|$: indeed, $X_n-\theta/L=(X-\theta)/L$, and division by the positive $L$ preserves the corresponding strict inequality for absolute values. Therefore the two events have equal uniform probability. Substituting the normalized shift into the bound gives exactly the claimed expression. The norm normalization uses the scaling law for the uniform $L^p$ norm (`uniformLpNorm_const_mul`).

**Key facts.** `FABL.uniformLpNorm_const_mul`, `FABL.IsHypercontractiveRandomVariable.const_mul`, `FABL.translated_anticoncentration_normalized`.
