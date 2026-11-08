<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Build/NDClockHostRun.lean :: Turing.ClockHost.inLeft_succ -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Recursive Leftward Head Movement

**Claim.** For every valid input-head position and every $j$, $j+1$ successive clamped leftward moves equal one leftward move applied after $j$ such moves.

**Proof.** Induct on $j$, with the initial head position generalized so the induction hypothesis applies to any starting position. At $j=0$, the defining equations for the repeated-move function give the claimed identity directly. For the successor case, unfold one recursive step: the computation first moves the starting position left and then performs the remaining $j$ moves. Apply the induction hypothesis to that new starting position; the result is exactly one left move after the $j$-move result from the original position.
