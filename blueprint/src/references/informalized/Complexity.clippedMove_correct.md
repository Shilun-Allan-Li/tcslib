<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Robustness/ObliviousCandidate.lean :: Complexity.clippedMove_correct -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Clipped Direction Gives Head Displacement

**Claim.** For any input length parameter $n$, head position $p$, and direction $d$, the moved head position, shifted down by one, equals the original shifted position plus the clipped direction.

**Proof.** Split into the three possible directions. For a zero direction, the head stays put and the clipped direction is zero. For a negative direction, the head-position formula says the new position is $p-1$ (`Turing.FinTM.moveInputPos_neg_val`). At the left boundary $p=0$, clipping replaces the attempted negative move by zero, giving the claimed equality; away from that boundary, the move is not clipped, and the integer identity follows by arithmetic. For a positive direction at the right boundary $p=n+1$, the head is clamped there and the attempted move is clipped to zero. Away from that boundary, the positive-move formula gives new position $p+1$ (`Turing.moveInputPos_pos_of_ne_right`), and the clipped direction remains positive, yielding the equality.

**Key facts.** `Turing.FinTM.moveInputPos_neg_val`, `Turing.moveInputPos_pos_of_ne_right`.
