<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/SpaceComplexity/Machines/Parse.lean :: Complexity.LogProg.cmpReturn -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Comparison Return Run

**Claim.** From the return state at register-head position $k-1$, the machine reaches the selected yes or no state, resets the input head to position $1$, and returns the register head to $0$, with the stated bounds on all earlier register-head positions.

**Proof.** First apply the register-backtracking fact (`regBack_x`) to the state $j_{RB}(b)$. Starting at position $k-1$, it scans right through the represented register word, then moves left once to position $0$ and enters $j_{I1}(b)$. It takes $k+1$ steps; throughout this part, the register head is at least $-1$ and at most its starting position, hence at most the word length. Its hypotheses follow from the stipulated return transition and from the buffer representation of the register.

Next apply the rewind fact (`rewind_x`) from $j_{I1}(b)$ at register position $0$. It moves the input head left to its boundary and then right to position $1$, entering the selected state $yes$ or $no$; the register head stays at zero and each visited state is not a call state. Concatenate these runs using the run-addition law. For times before the first phase ends, use the bounds from register backtracking; for later earlier times, use the rewind bounds and the fact that position zero lies in the required interval.

**Key facts.** `Complexity.LogProg.regBack_x`, `Complexity.LogProg.rewind_x`, `Complexity.LogProg.rrun_add`.
