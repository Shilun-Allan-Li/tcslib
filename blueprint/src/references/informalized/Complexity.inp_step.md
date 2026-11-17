<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/PSubsetPPolyConfigStep.lean :: Complexity.inp_step -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Input Head Position After One Step

**Claim.** After one step, the input-head position equals $p$ exactly when the stated Boolean condition for the halted case or the transition’s head movement holds.

**Proof.** If the configuration is halted, one step leaves it unchanged, so the new position is $p$ exactly when the current position is $p$. Otherwise, the transition supplies a head movement. For a right move, the new position is the smaller of the current position plus one and the right boundary $|w|+1$ (the fact `moveInputPos_pos_val`). Thus it is $p$ either at the left boundary $p=0$, where a move is clamped, or when the current position is $p-1$ and $p\ge1$. For a stationary move, the position is unchanged (`moveInputPos_zero`), giving precisely the condition that the current position is $p$. For a left move, the new position is the current position minus one (the fact `moveInputPos_neg_val`); accounting for the boundary and the nonnegative range of positions, this equals $p$ exactly when $p=|w|+1$ or the current position is $p+1$. The hypothesis $p\le |w|+1$ and the configuration’s position bound ensure these cases cover the possible positions.

**Key facts.** `Complexity.moveInputPos_pos_val`, `Turing.moveInputPos_zero`, `Complexity.moveInputPos_neg_val`.
