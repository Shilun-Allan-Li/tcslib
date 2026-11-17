<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/ClassPSPACE/Games.lean :: Complexity.Game.playOut_eq_iterate -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Play as Repeated Single Moves

**Claim.** For any two strategies and any number of moves $r$, the history after $r$ moves equals the result of applying the single-move update $r$ times to the empty history.

**Proof.** Induct on $r$. At zero moves, both histories are empty. For the successor step, the history after $r+1$ moves is obtained by applying one single-move update to the history after $r$ moves (`playOut_succ_ply`). Substitute the induction hypothesis, then the definition of function iteration identifies this with $r+1$ updates applied to the empty history.

**Key facts.** `Complexity.Game.playOut_succ_ply`.
