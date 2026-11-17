<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter07/HastadThreeSat.lean :: FABL.hastadThreeSatOXRError_tendsto_zero -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Vanishing Three-SAT OXR Error

**Claim.** For each natural number $t$, the three-SAT OXR error tends to $0$ as $\varepsilon$ tends to $0$ through positive values.

**Proof.** Define $g(\varepsilon)=\min\left(1,\frac{1}{4}\sqrt{\varepsilon/(1-\varepsilon)^{t-1}}\right)$. The denominator is continuous at $0$ and equals $1$ there, so the quotient is continuous at $0$; taking its square root, dividing by $4$, and taking the minimum with the constant function $1$ preserve continuity. Thus $g$ is continuous at $0$. Since $g(0)=0$, continuity implies that $g(\varepsilon)$ tends to $0$ as $\varepsilon$ approaches $0$ through positive values. Also, all sufficiently small positive $\varepsilon$ satisfy $\varepsilon<1$, so the defining formula for the OXR error agrees with $g$ on a neighborhood of $0$ within that domain. The two functions therefore have the same limit there.
