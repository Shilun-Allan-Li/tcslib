<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/SpaceComplexity/Logspace/ISCountGenCorrect.lean :: Complexity.LogProg.ISGen.gKv_mono -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Monotonicity of the Exponential Bound

**Claim.** For natural numbers $E,\ell,s,s'$, if $s\le s'$, then $2^{2E\ell+2Es}\le 2^{2E\ell+2Es'}$.

**Proof.** From $s\le s'$, multiplication by the nonnegative number $2E$ gives $2Es\le 2Es'$. Adding the common term $2E\ell$ preserves the inequality. The function $n\mapsto 2^n$ is monotone on natural numbers, so exponentiating gives the result.
