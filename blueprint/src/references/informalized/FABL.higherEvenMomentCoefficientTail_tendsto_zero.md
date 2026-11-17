<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter09/HypercontractiveMomentSharpness.lean :: FABL.higherEvenMomentCoefficientTail_tendsto_zero -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Vanishing Higher-Moment Tail

**Claim.** For a finite probability space and fixed $r,j$, the higher even-moment coefficient tail at $t=1/(m+1)$ tends to zero as $m$ tends to infinity.

**Proof.** The tail is a finite sum over $l$ in the range from $0$ to $r$. For each such $l$, if $j<l$, then the exponent $2l-2j$ is positive, so $(1/(m+1))^{2l-2j}$ tends to zero; multiplying by the fixed coefficient preserves convergence to zero. If $j\ge l$, that summand is identically zero. Since a finite sum of sequences converging to zero also converges to zero, the whole tail tends to zero.
