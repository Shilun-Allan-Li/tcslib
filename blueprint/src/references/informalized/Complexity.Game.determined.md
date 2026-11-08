<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/ClassPSPACE/Games.lean :: Complexity.Game.determined -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Determinacy of the Boolean Game

**Claim.** In the finite alternating Boolean game, either the first player has a strategy guaranteeing that the final predicate is true, or the second player has a strategy guaranteeing that it is false.

**Proof.** Consider the position value of the empty history with $n$ moves remaining. If this value is false, choose the second player's greedy strategy. The game history after $n$ moves is the result of iterating the single-move update from the empty history (`playOut_eq_iterate`); the winner-from-position-value result then shows, for every first-player strategy, that the final predicate is false (`winner_of_value`). Thus the second player wins. If the initial position value is true, choose the first player's greedy strategy instead. The same position-value result, now for every second-player strategy, shows that the final predicate is true. These two cases establish the claimed alternative.

**Key facts.** `Complexity.Game.playOut_eq_iterate`, `Complexity.Game.winner_of_value`.
