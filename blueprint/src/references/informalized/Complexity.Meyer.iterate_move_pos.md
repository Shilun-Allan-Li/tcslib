<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/MeyerTableau.lean :: Complexity.Meyer.iterate_move_pos -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Iterated rightward head movement

**Claim.** After $a$ successive right moves from position $p$, the resulting position is $\min(p.val+a,n+1)$.

**Proof.** Induct on $a$, generalizing the starting position. With zero moves, the position is $p$, which is the displayed minimum because $p.val\le n+1$. For the successor case, use the induction hypothesis for the position after the first move. If the head starts at the right boundary, it remains there (`Turing.moveInputPos_rightBoundary`), so the minimum remains $n+1$. Otherwise one right move increases its value by one (`Turing.moveInputPos_pos_of_ne_right`); the minimum formula then follows by arithmetic.

**Key facts.** `Turing.moveInputPos_rightBoundary`, `Turing.moveInputPos_pos_of_ne_right`.
