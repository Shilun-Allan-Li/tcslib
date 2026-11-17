<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/SpaceComplexity/Machines/MARM.lean :: Complexity.LogProg.mrun_succ -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Successor-Time Run Identity

**Claim.** Running from a configuration for $n+1$ steps gives the same result as taking one step first and then running for $n$ further steps.

**Proof.** The run is the iterate of the one-step transition function. The iterate-at-successor law writes the $(n+1)$-fold iterate applied to the initial configuration as the $n$-fold iterate applied after one transition. This is exactly the asserted identity.
