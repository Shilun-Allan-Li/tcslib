<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/ClassPSPACE/Games.lean :: Complexity.Game.playOut_succ_ply -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Successor Play Update

**Claim.** After $r+1$ moves, the history is obtained by applying one single-move update to the history after $r$ moves, with the moving player chosen according to whether that history has even or odd length.

**Proof.** The recursive definition of play at a successor step takes the history after $r$ moves and appends the next Boolean move. The move is selected from the first player's strategy when the history length is even and from the second player's strategy when it is odd. This is exactly the single-move update applied to that history.
