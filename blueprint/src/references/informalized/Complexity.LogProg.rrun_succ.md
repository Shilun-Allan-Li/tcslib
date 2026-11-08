<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/SpaceComplexity/Machines/Compile.lean :: Complexity.LogProg.rrun_succ -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Successor Recurrence for a Run

**Claim.** For a register program $P$, oracle $\mathcal O$, configuration $c$, and $n\in\mathbb N$, the run of length $n+1$ from $c$ is obtained by taking one step from the configuration reached after $n$ steps.

**Proof.** The run is the iteration of the one-step transition. The iterate-successor law expresses the $(n+1)$st iterate as one application of that transition after the $n$th iterate. Applying this identity to $c$ gives the stated recurrence.
