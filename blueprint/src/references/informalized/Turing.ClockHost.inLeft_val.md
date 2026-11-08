<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Build/NDClockHost.lean :: Turing.ClockHost.inLeft_val -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Position After Repeated Left Moves

**Claim.** After $j$ clamped leftward moves from position $ip$, the resulting position has value $ip-j$, with subtraction truncated in the natural numbers.

**Proof.** Induct on $j$, generalizing the starting position. The zero-step case is immediate. For the successor step, unfold the recursive definition and use the induction hypothesis to reduce the value to the value after one clamped left move, minus $j$. If the starting position is zero, a left move stays at zero, so the desired truncated subtraction formula follows. Otherwise, the move decreases its value by one, by the fact that a clamped negative move from a nonzero position has value one less (`Turing.moveInputPos_neg_of_ne_left`). The resulting natural-number identity is $ip.val-1-j=ip.val-(j+1)$.

**Key facts.** `Turing.moveInputPos_neg_of_ne_left`.
