<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/GaussianSpace/InvarianceTruncation.lean :: BooleanAnalysis.GaussianSpace.Invariance.invariance_cutoff_power_le -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Cutoff Power Comparison

**Claim.** For $0<\varepsilon\le1$ and $\delta\le1/20$, the stated product of powers of $2$ and $\varepsilon$ is bounded above by $\varepsilon^{\delta/3}$.

**Proof.** Rewrite each real power as an exponential and combine the factors. The desired inequality then reduces, by monotonicity of the exponential, to an inequality between exponents. Using $\log(1/\varepsilon)=-\log\varepsilon$, it is enough that $\delta/3\le1/4-(\log2)/3$, because $\log\varepsilon\le0$ reverses the comparison when multiplied by it. The estimates $\delta\le1/20$ and $\log2\le7/10$ imply this coefficient inequality: indeed $1/60\le1/4-7/30$. Multiplying by the nonpositive $\log\varepsilon$ in the appropriate direction proves the exponent comparison, and hence the claim.
