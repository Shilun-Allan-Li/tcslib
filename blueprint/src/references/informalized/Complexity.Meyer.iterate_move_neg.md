<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/MeyerTableau.lean :: Complexity.Meyer.iterate_move_neg -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Repeated leftward head movement

**Claim.** After $a$ successive left moves from position $p$, the head’s value is $p.val-a$, with natural-number subtraction truncated at zero.

**Proof.** Induct on the number $a$ of moves, generalizing the starting position. With no moves, the position is unchanged, giving the formula. For the successor case, apply the induction hypothesis to the position after the first move. If the starting position is the left boundary, one left move leaves it at zero (`Turing.moveInputPos_leftBoundary`), and the remaining moves satisfy the truncated-subtraction formula. Otherwise a left move lowers the position by exactly one (`Turing.moveInputPos_neg_of_ne_left`); combining this with the induction hypothesis gives the stated subtraction identity.

**Key facts.** `Turing.moveInputPos_leftBoundary`, `Turing.moveInputPos_neg_of_ne_left`.
