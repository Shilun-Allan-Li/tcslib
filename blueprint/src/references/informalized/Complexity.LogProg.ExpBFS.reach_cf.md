<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/SpaceComplexity/ExpBFS/Run.lean :: Complexity.LogProg.ExpBFS.reach_cf -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Reachability Under Equal State Data

**Claim.** If a configuration reaches the configuration with label $l$, register state $st$, memory $M$, and head position $p$, then equalities $st=st'$ and $p=p'$ give the same reachability statement with state $st'$ and head position $p'$.

**Proof.** The endpoint configuration is built from the label, register state, memory, and head position. Replacing the state and head position by equal values leaves that endpoint unchanged. Thus the same run and the same guard condition at every intermediate time witness reachability of the rewritten endpoint.
