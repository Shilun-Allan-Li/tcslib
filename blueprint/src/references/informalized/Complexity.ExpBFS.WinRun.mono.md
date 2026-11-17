<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/SpaceComplexity/ExpBFS/Radius.lean :: Complexity.ExpBFS.WinRun.mono -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Monotonicity of the Window Bound

**Claim.** If every configuration reached along every prefix of $w$ lies in the window of radius $s$, and $s\le s'$, then every such configuration lies in the window of radius $s'$ as well.

**Proof.** Fix any prefix length $j\le |w|$. The hypothesis puts the corresponding configuration in the radius-$s$ window. Enlarging the radius preserves the window condition: each head-position bound remains true, and every cell outside the larger window is also outside the smaller one and hence blank (\texttt{inWin\_mono}). Applying this to each allowed $j$ proves the claim.

**Key facts.** `Complexity.ExpBFS.inWin_mono`.
