<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/SpaceComplexity/Logspace/PathWalkMachine.lean :: Complexity.LogProg.PReg.reg -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Register Bounds for a Configuration

**Claim.** If each of the nine register values in a record is at most $B$, then every register value in the configuration formed from its register vector, any control label, and any Boolean result is at most $B$.

**Proof.** The configuration's register component is the record's nine-entry vector; the control label and optional result do not change that vector. Each coordinate of the vector is one of the nine named register values. The assumed nine bounds therefore cover every coordinate.
