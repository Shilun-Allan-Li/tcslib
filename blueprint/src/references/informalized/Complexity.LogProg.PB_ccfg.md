<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/SpaceComplexity/Machines/CleanSweep.lean :: Complexity.LogProg.PB_ccfg -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Head Bounds for the Combined Configuration

**Claim.** If both $k$-tape collections have every head position bounded in absolute value by $B$, then the configuration formed by concatenating those collections has the same bound on all $2k$ work-tape heads.

**Proof.** Take any tape index in the combined configuration. The finite-index sum decomposition (`Fin.addCases`) places it either in the first collection or in the second. In the first case, concatenation makes its head position the corresponding position from the first collection, so the first bound applies; in the second case it is the corresponding position from the second collection, so the second bound applies. In either case its absolute value is at most $B$.
