<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter09/HypercontractiveApplications.lean :: FABL.interpolation_constant_le_exp -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Interpolation constant exponential bound

**Claim.** For $c\ge 0$ and $\varepsilon>0$, $(1+\varepsilon)^{c(1/\varepsilon+1/2)}\le \exp(c(1+\varepsilon/2))$.

**Proof.** Since $1+\varepsilon>0$, write the power as an exponential with exponent $c(1/\varepsilon+1/2)\log(1+\varepsilon)$. For positive $u$, the logarithm satisfies $\log u\le u-1$; taking $u=1+\varepsilon$ gives $\log(1+\varepsilon)\le\varepsilon$. The multiplier $c(1/\varepsilon+1/2)$ is nonnegative, so multiplying preserves the inequality. The resulting exponent simplifies, using $\varepsilon>0$, to $c(1+\varepsilon/2)$. Monotonicity of the exponential yields the bound.
