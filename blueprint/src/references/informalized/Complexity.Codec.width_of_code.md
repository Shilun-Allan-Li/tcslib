<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/SpaceComplexity/Codec/Deciders.lean :: Complexity.Codec.width_of_code -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Binary width from a configuration code

**Claim.** If the configuration word for $C$ with window parameter $s$ has length at most $|y|$, then the binary expansion of $s$ is no longer than the binary expansion of $|y|$.

**Proof.** Binary-expansion length is monotone in its natural-number argument (`length_bits_mono`), so it suffices to show $s\le |y|$. The configuration word has length $W_N(2s+1)+wP(|x|)+1$ (`length_cfgWord`), which is at least $2s+1$ because $W_N\ge1$ and the remaining terms are nonnegative. By hypothesis this length is at most $|y|$, so $s\le |y|$. Monotonicity now gives the desired inequality between binary widths.

**Key facts.** `Complexity.Codec.length_cfgWord`, `Complexity.LogProg.length_bits_mono`.
