<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/CodeSimulator.lean :: Turing.MachineFormat.binaryGuard_done -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Halting of the Binary Guard Machine

**Claim.** Under the stated bounds on the input position and counter value, the binary guard machine reaches its done state within the stated time bound, preserves the output, and has the asserted input position; before that time it is neither done nor escape.

**Proof.** Write $d$ for the value represented by the counter word. Each completed guard block advances the input position by $b+1$ and returns to the initial guard phase, while preserving the output. The orbit formula for these blocks (`guardBlock_orbit`) therefore identifies the configuration after $r$ rounds as the guard configuration at position $j+(b+1)r$. The fit assumption ensures this position remains within the input for every $r\le d$.

For each round $r<d$, the block begins in its initial phase, takes positive time, and does not reach its terminal phase before the block ends (`guardBlock_segment`). These facts supply the round hypotheses for the counter-loop result `counterLoopTM_run_done`: the loop decrements the counter once per round, performs all $d$ blocks, and then reaches done. At that point the orbit formula gives input position $j+(b+1)d+1$; the output is unchanged, and the loop result ensures that at every earlier time the state is neither done nor escape.

For the time estimate, `counterLoop_time_le` bounds the total block and counter overhead by $d(b+1)+4d+2|w|+2$. Since $d\le (b+1)d$ and $(b+1)d\le |x|$, this is at most $5|x|+2|w|+2$, as required.

**Key facts.** `Turing.MachineFormat.guardBlock_orbit`, `Turing.MachineFormat.guardBlock_segment`, `Turing.counterLoopTM_run_done`, `Turing.counterLoop_time_le`.
