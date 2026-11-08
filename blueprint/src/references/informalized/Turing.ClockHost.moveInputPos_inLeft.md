<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Build/NDClockHost.lean :: Turing.ClockHost.moveInputPos_inLeft -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Right Move from the Left Boundary

**Claim.** If the input head starts at position $ip$ and is moved left with clamping $j$ times, where $ip\le j$, then moving right once gives position $1$.

**Proof.** The position after $j$ clamped left moves has value $ip-j$ (`inLeft_val`). Since $ip\le j$, this value is zero, so the head is at the left boundary. A positive move from position zero advances to position one: the head is not at the right boundary, and the positive-move rule gives value $0+1$ (`moveInputPos_pos_of_ne_right`).

**Key facts.** `Turing.ClockHost.inLeft_val`, `Turing.moveInputPos_pos_of_ne_right`.
