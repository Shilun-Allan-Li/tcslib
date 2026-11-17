<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Configuration.lean :: Turing.workTapePos_apply_le -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Bound on work-head movement

**Claim.** For every single-step action, configuration, and work-tape index, the absolute difference between the head position after applying the action and its position before is at most $1$.

**Proof.** Applying the action changes the chosen work-head position from its old value $p$ to $p+m$, where $m$ is its movement sign. Subtracting the old position leaves exactly the integer cast of that sign. Each sign has absolute value at most $1$, so the claimed bound follows.
