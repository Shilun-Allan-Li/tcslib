<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/StateRenaming.lean :: Turing.MultiTapeTM.relabelState_visitedByTapeHead -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Preservation of Visited Cells

**Claim.** For each work tape, state relabelling preserves the set of integer positions visited by its head through any given time.

**Proof.** The visited set consists of the head positions at each time from zero through $t$. At each such time, the run of the relabelled machine is the state-relabelling of the original run (`relabelState_runFrom_init`). Mapping a configuration’s state changes no tape-head position, so the two runs contribute the same position at every time. Their sets of visited positions are consequently equal.

**Key facts.** `Turing.MultiTapeTM.relabelState_runFrom_init`.
