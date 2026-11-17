<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/SpaceComplexity/Machines/Lib.lean :: Complexity.LogProg.rrun_one -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# One Step of a Run

**Claim.** For a register program $P$, oracle $\mathcal O$, and configuration $c$, running the program for one step from $c$ gives its one-step successor configuration.

**Proof.** A run of length one is, by definition, the first iterate of the one-step transition applied to $c$. This is exactly the one-step successor configuration.
