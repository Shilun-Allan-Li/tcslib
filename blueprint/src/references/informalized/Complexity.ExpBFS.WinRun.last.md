<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/SpaceComplexity/ExpBFS/Radius.lean :: Complexity.ExpBFS.WinRun.last -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Final Configuration of a Window-Bounded Run

**Claim.** If every configuration reached by following any prefix of $w$ lies in the window of radius $s$, then the configuration reached by following all of $w$ lies in that window as well.

**Proof.** By definition, the hypothesis applies to every prefix length $j\le |w|$. Take $j=|w|$. The prefix of $w$ of this full length is $w$ itself, so the asserted final configuration is one of those covered by the hypothesis.
