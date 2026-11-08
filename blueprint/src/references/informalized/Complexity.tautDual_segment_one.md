<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/ClassNP/Tautology.lean :: Complexity.tautDual_segment_one -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Single-Step Anchor-Free Segment

**Claim.** If one step from $c$ reaches $d$ and $c$ is not in the anchor state, then the run from $c$ is an anchor-free segment of length $1$.

**Proof.** The one-step endpoint is $d$ by hypothesis. The only natural number strictly less than $1$ is $0$, and the run at time zero is the starting configuration $c$. Its state is not the anchor by hypothesis, so the segment has no earlier anchor-state visit.
