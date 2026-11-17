<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/ClassNP/SAT.lean :: Complexity.satAppend_clean -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Clean Return of the Appender

**Claim.** For every Boolean input word $x$ and work-tape word $w$, the appender has a positive halting time bounded by $2|w|+3|x|+6$, has not halted at any earlier time, and at that time is in the specified clean configuration holding $w++x$.

**Proof.** The proof first assembles the appender's phases. Starting with $w$ on the tape and the input head at its initial position, the seek lemma moves from the start of $w$ to its end and enters the copying state (`Complexity.satAppend_seek`). The copy lemma then appends the entire input $x$ to $w$ and enters the rewind state with the input head at its endpoint (`Complexity.satAppend_copy`). The rewind lemma returns the work head to zero and enters the state from which the input head is scanned back to its initial position (`Complexity.satAppend_rewind`). For that final scan, the timed-rewind result supplies a time $r$ bounded by the input-head position plus two, and puts the machine in the halting state with the input head restored (`Turing.FinTM.timed_rewind`).

The proof identifies the specified initial configuration with the appender's start configuration, and checks that after these phases the tape contents and head positions match the desired clean configuration. The run-addition identity allows the phase runs to be concatenated in order (`Turing.MultiTapeTM.runFrom_add`). Together the phase lengths give a time at which the target halted configuration is reached. The lemma that extracts the first halt from any run known to halt at time $t$ then provides a positive time no later than that run, with no earlier halt and the same halted configuration (`Complexity.sat_call_first_halt`). Finally, the explicit bound on the rewind scan and the phase lengths yield $t\le 2|w|+3|x|+6$.

**Key facts.** `Complexity.satAppend_seek`, `Complexity.satAppend_copy`, `Complexity.satAppend_rewind`, `Turing.FinTM.timed_rewind`, `Turing.MultiTapeTM.runFrom_add`, `Complexity.sat_call_first_halt`.
