<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/CounterProgRun.lean :: Complexity.CounterProg.exists_tm -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Simulation of halted counter programs

**Claim.** If the counter program started at its initial state halts after $t$ steps, then the compiled Turing machine, on input $x$, produces the same output by time $t(2t+3)$, with some space usage.

**Proof.** First identify the Turing machine's initial configuration with the encoding of the counter program's initial state. Apply the simulation theorem (`sim_run`) with register bound $B=t$: since every register starts at zero, after at most $t$ steps every register value is at most $t$. It gives a time $t'\le t(2t+3)$ at which the machine reaches the encoding of the counter program's state after $t$ steps. The hypothesis says that state is halted, so the simulated machine configuration at time $t'$ is halted as well. A halted machine remains at the same configuration for every later number of steps: decompose the total time as $t'+(t(2t+3)-t')$, use the run composition law (`runFrom_add`), and then use the fact that a halted configuration is fixed by further running (`runFrom_of_halt`). Thus at the stated time the machine is halted and its output is the encoded run's output. The characterization of computation in time (`computesInTime_iff`) now gives the required computation; its existential space component supplies some space usage.

**Key facts.** `Complexity.CounterProg.sim_run`, `Turing.FinTM.computesInTime_iff`, `Turing.MultiTapeTM.runFrom_add`, `Turing.MultiTapeTM.runFrom_of_halt`.
