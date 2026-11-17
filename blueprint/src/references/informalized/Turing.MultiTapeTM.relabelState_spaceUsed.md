<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/StateRenaming.lean :: Turing.MultiTapeTM.relabelState_spaceUsed -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Preservation of Space Use

**Claim.** Relabelling the states of a machine leaves its total space use through any given time unchanged.

**Proof.** Expand total space use as the sum, over work tapes, of the number of positions visited by each tape head. For each tape, the visited-position set of the relabelled machine equals that of the original machine (`relabelState_visitedByTapeHead`). Taking cardinalities therefore gives equal space use on each tape, and summing these equalities over the tapes proves the result.

**Key facts.** `Turing.MultiTapeTM.relabelState_visitedByTapeHead`.
