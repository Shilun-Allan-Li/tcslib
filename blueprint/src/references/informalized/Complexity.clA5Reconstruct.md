<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CookLevin/Hardness.lean :: Complexity.clA5Reconstruct -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Reconstruction of Computation Snapshots

**Claim.** Under the stated initial, transition, input-slice, and work-tape-slice assumptions, every raw block through time $T$ is the encoding of the corresponding run snapshot.

**Proof.** Proceed by strong induction on the time $t$, proving the assertion for all times at most $T$. At time zero it is the assumed initial encoding. For a successor time $t+1$, use the block extensionality fact (`Complexity.clBlock_ext`): it suffices to identify the state, input, and each work-tape slice. The state slice assumption says that the next block encodes the state obtained by applying the transition rule to the decoded block at time $t$. By induction that decoded block is the actual snapshot, since decoding an encoded snapshot recovers it (`Complexity.clBlockDecode_encode`); the snapshot state evolves by exactly this transition (`Complexity.snapshotAt_state_succ`). For the input slice, the given hypothesis supplies the scanned input symbol, which is the input component of the actual snapshot by `Complexity.snapshotAt_inputSymbol`. For each work tape, the slice hypothesis identifies its symbol with the value prescribed by the most recent visit. If there is no such visit, both sides give blank. If the most recent visit is at time $s$, the specification of `prevVisit` ensures $s<t+1$, so strong induction applies at $s$; decoding the resulting encoded snapshot gives its actual value at that tape and head position. This is exactly the work-symbol description of the snapshot (`Complexity.snapshotAt_workSymbol`). The three component identifications give equality of the blocks.

**Key facts.** `Complexity.clBlock_ext`, `Complexity.clBlockDecode_encode`, `Complexity.snapshotAt_state_succ`, `Complexity.snapshotAt_inputSymbol`, `Complexity.clPrev_spec`, `Complexity.snapshotAt_workSymbol`.
