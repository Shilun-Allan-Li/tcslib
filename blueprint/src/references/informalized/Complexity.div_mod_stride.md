<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/PSubsetPPolyConfig.lean :: Complexity.div_mod_stride -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Stride quotient and remainder

**Claim.** For stride $s=k(M)(2T+1)+N+3$, if $o<s$, then $ts+o$ has quotient $t$ and remainder $o$ upon division by $s$.

**Proof.** The stride is positive (Complexity.stride_pos). Reorder the sum as $o+ts$. Since $o<s$, division of $o$ by $s$ has quotient zero; adding $ts$ therefore gives quotient $t$. For the remainder, adding a multiple of the divisor does not change the remainder, so the remainder of $o+ts$ is the remainder of $o$, which is $o$ because $o<s$.

**Key facts.** `Complexity.stride_pos`.
