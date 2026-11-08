<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/SpaceComplexity/Machines/ARMRun.lean :: Complexity.LogProg.arun_succ -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Successor Step of an Abstract Run

**Claim.** For any register program, oracle, input, configuration, and natural number $n$, a run of $n+1$ steps equals a run of $n$ steps started after one abstract step.

**Proof.** An abstract run is the iteration of the one-step transition function. The successor-iterate identity rewrites its $(n+1)$st iterate as the $n$th iterate applied after one transition. This is exactly the stated equality.
