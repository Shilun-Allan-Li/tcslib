<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/ClassNP/SAT.lean :: Complexity.satMax_prefix -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Counter replay prefix

**Claim.** For every $r\le n$, after $r$ steps from the streaming entry configuration with unary counter length $n$, arbitrary buffer, and empty output, the machine remains in that state, with input and buffer unchanged, counter head at $r$, and output consisting of $r$ true bits.

**Proof.** We induct on $r$. For $r=0$, the run is the initial configuration itself, so the description holds. Suppose it holds at $r$ and that $r+1\le n$. The counter head at $r$ reads true because $r<n$, by the counter-read description (Complexity.satRedCounter_read). Consequently the next transition stays in the streaming state, advances the counter head by one, and emits one true bit, while leaving the input and buffer unchanged. The input head does not move, since a zero movement preserves its position (Turing.moveInputPos_zero); the tape contents and head positions follow directly from the specified transition and action. Appending the new true bit to the existing string of $r$ true bits gives the string of $r+1$ true bits. The correspondence between a run of $r+1$ steps and one transition after the $r$-step run is the successor-step identity (Turing.MultiTapeTM.runFrom_succ_eq_step').

**Key facts.** `Turing.MultiTapeTM.runFrom_succ_eq_step'`, `Complexity.satRedCounter_read`, `Turing.moveInputPos_zero`.
