<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CookLevin/Hardness.lean :: Complexity.clElapsed_width -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Binary Width Bounded by Elapsed Time

**Claim.** If $n\le t$, then the binary representation of $n$ has at most $t$ bits.

**Proof.** Since $t<2^t$, the inequality $n\le t$ implies $n<2^t$. The binary width bound (`Complexity.clCount_width`) applied with width $t$ now gives $n$ at most $t$ bits.

**Key facts.** `Complexity.clCount_width`.
