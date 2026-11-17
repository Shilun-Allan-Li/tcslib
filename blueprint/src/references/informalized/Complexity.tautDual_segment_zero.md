<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/ClassNP/Tautology.lean :: Complexity.tautDual_segment_zero -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Empty Anchor-Free Segment

**Claim.** For every binary input $x$ and configuration $c$, the run from $c$ is an anchor-free segment of length $0$.

**Proof.** At time zero the run is still at $c$, so the endpoint condition holds. There is no natural number strictly less than zero, hence there are no earlier times at which an anchor-state visit could occur.
