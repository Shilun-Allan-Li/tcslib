<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/ClassNP/TMSAT.lean :: Complexity.tmsat_take_double -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Counting a doubled data block

**Claim.** If two consecutive bits of $x$ at positions $i$ and $i+1$ are both $b$, then after two steps from the specified state $0$ configuration, the prefix extractor has advanced its input head by two, increased its unary work tape and work-head position by one, and remains in state $0$ with empty output.

**Proof.** The first transition reads the bit at position $i$ (`Complexity.tmsat_take_read`). In state $0$, either possible bit sends the machine to its corresponding intermediate state, advances the input head one position, and leaves the work tape and output unchanged. The second transition reads the equal bit at position $i+1$. In either intermediate state, this transition writes a $1$ at the current work-head position, advances that head and the input head by one, and returns to state $0$. The work-tape update changes the unary tape from $1^m$ to $1^{m+1}$, by the update identity `Complexity.polyTape_write`. The two-step run is identified with these successive transitions using the run-from-zero and successor-step rules (`Turing.MultiTapeTM.runFrom_zero`, `Turing.MultiTapeTM.runFrom_succ_eq_step`). The input-head advances are valid because the stated length bound keeps the head short of the right boundary, as expressed by `Turing.moveInputPos_pos_of_ne_right`.

**Key facts.** `Complexity.tmsat_take_read`, `Turing.MultiTapeTM.runFrom_succ_eq_step`, `Turing.MultiTapeTM.runFrom_zero`, `Turing.moveInputPos_pos_of_ne_right`, `Complexity.polyTape_write`.
