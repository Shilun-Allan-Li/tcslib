<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/SpaceComplexity/ExpBFS/Radius.lean :: Complexity.ExpBFS.WinRun.snoc -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Appending a Choice Bit to a Window-Bounded Run

**Claim.** If every configuration along every prefix of $w$ lies in the radius-$s$ window, and the configuration reached after $wb$ also lies in that window, then every configuration along every prefix of $wb$ lies in it.

**Proof.** Consider a prefix length $j\le |w|+1$. If $j<|w|+1$, the first $j$ bits of $wb$ are exactly the first $j$ bits of $w$, so the required configuration lies in the window by the hypothesis for $w$. If $j=|w|+1$, the prefix is all of $wb$, and the stated endpoint assumption supplies the window condition. These cases cover every permitted prefix length.
