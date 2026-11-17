<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/PSubsetPPolyConfig.lean :: Complexity.cfgExp_snapIdx -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Snapshot-position encoding

**Claim.** At the tableau index assigned to the snapshot at time $t$, the configuration encoding equals the snapshot encoding at time $t$.

**Proof.** The indexing lemma identifies the tableau position of the snapshot index as the snapshot at time $t$ (`Complexity.cfgPos_snapIdx`). By definition, the configuration encoding at a snapshot position is the snapshot encoding at that time. The equality follows.

**Key facts.** `Complexity.cfgPos_snapIdx`.
