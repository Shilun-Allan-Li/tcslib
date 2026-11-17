<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Robustness/SingleTape.lean :: Turing.FinTM.dg_read_boundary -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Transition at a Read Boundary

**Claim.** At a read-phase boundary, the simulator tests whether any flagged tape head moves right under the source transition. If so, it pauses in the right-growth phase at counter zero; otherwise it takes the simulator transition from right-growth phase at counter $k$ on the same boundary marker.

**Proof.** Unfold the simulator transition in the read state. Since the scanned work symbol is the boundary marker, the boundary case of the read-state definition applies. It computes the source transition using the retracted input symbol and the tape symbols stored in $s$, then tests whether a tape flagged by $s$ moves right. In the positive case, the defined transition is the stationary move to right-growth phase at counter zero. In the negative case, the definition uses the old sweep-machine transition from right-growth phase at counter $k$, with the same boundary input. These are exactly the two branches in the statement.
