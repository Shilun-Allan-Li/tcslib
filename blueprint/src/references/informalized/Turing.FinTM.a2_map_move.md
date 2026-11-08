<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Build/Catalog.lean :: Turing.FinTM.a2_map_move -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Effect of a structured simulator action

**Claim.** Applying the specified simulator action moves the input head by $m_i$, moves the two buffer heads by $m_a$ and $m_b$, emits the optional bit, and otherwise preserves the buffers, yielding the stated configuration.

**Proof.** The action makes no writes, so each work-tape function remains unchanged. The first two tape blocks are the two buffer tapes, and the remaining blocks are the simulator's other tapes; splitting these blocks shows that all tape contents are preserved. The action adds the prescribed signed movement to each of the first two head positions and leaves the other heads, whose movement is zero, unchanged. Its input movement is by definition the new input-head position. Finally, applying an optional output bit appends its singleton list when present and appends nothing when absent. These componentwise equalities identify the resulting configuration.
