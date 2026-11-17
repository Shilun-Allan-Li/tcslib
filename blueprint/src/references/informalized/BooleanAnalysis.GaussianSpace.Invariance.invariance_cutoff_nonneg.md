<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/GaussianSpace/InvarianceTruncation.lean :: BooleanAnalysis.GaussianSpace.Invariance.invariance_cutoff_nonneg -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Nonnegative Cutoff Exponent

**Claim.** For every real $\varepsilon$ with $0<\varepsilon\le1$, the quantity $\log(1/\varepsilon)/3$ is nonnegative.

**Proof.** Since $0<\varepsilon\le1$, reciprocation gives $1\le1/\varepsilon$. The logarithm is nonnegative on numbers at least $1$, so $\log(1/\varepsilon)\ge0$. Dividing by the positive number $3$ preserves nonnegativity.
