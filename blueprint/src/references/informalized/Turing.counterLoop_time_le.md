<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Build/CounterLoop.lean :: Turing.counterLoop_time_le -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Counter loop time bound

**Claim.** If each of the first $d$ round durations is at most $B$, then their total duration plus the counter overhead through round $d$ is at most $dB+4d+2|w|+2$, when the binary value of $w$ is $d$.

**Proof.** There are $d$ terms in the sum of round durations, and each is at most $B$. Thus their sum is at most $dB$, by the finite-sum bound `Finset.sum_le_card_nsmul`. The counter overhead bound (`counterOverhead_le`) gives an upper bound of $4V(w)+2|w|+2$ for the overhead through $V(w)+1$ rounds. Since $V(w)=d$, this is $4d+2|w|+2$. Adding the two bounds proves the result.

**Key facts.** `Turing.counterOverhead_le`.
