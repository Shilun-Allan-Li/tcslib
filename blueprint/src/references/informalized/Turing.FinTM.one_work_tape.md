<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Robustness/SingleTape.lean :: Turing.FinTM.one_work_tape -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# One-Tape Simulation

**Claim.** Any finite Turing machine computing a function in time bound $T$ can be simulated by a finite machine with one work tape, using an enlarged alphabet and symbolwise encoding, within a quadratic time bound.

**Proof.** 1. If the original machine has no work tapes, retain its alphabet and input encoding and use the construction that adds an unused work tape. Its computation is preserved (`Turing.FinTM.unusedTape_computes`). Since $T(n)\le (T(n)+1)^2$, monotonicity of computation time gives the required bound with constant $1` (`Turing.FinTM.ComputesInTime.mono`).

2. Otherwise, the machine has at least one work tape. Choose the sweep alphabet, its encoding of the original symbols, and the one-work-tape sweep machine. For each input, choose the first time $\tau$ at which the original machine halts. Such a time exists by the assumed computation; it is at most $T(|x|)$, and the original machine is nonhalting at every earlier time. The sweep simulation lemma says that, through time $\tau$, the new machine's sweep computation represents the original run (`Turing.FinTM.sweep_run_to_halt`). At $\tau$, its state is therefore halting; its output is the encoded original output, since a machine's output stays unchanged after it halts (`Turing.MultiTapeTM.runFrom_output_eq_of_halt`). The sweep time bound is at most $(9k+6)(\tau+1)^2$ (`Turing.FinTM.sweepTime_le`), which is at most $(9k+6)(T(|x|)+1)^2$. This yields the stated constant and simulation.

**Key facts.** `Turing.FinTM.unusedTape_computes`, `Turing.FinTM.ComputesInTime.mono`, `Turing.FinTM.sweep_run_to_halt`, `Turing.MultiTapeTM.runFrom_output_eq_of_halt`, `Turing.FinTM.sweepTime_le`.
