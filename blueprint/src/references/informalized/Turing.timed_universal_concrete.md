<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Universal.lean :: Turing.timed_universal_concrete -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Concrete Time Bound for Universal Simulation

**Claim.** For each effective machine-coding scheme there is one finite-tape Boolean machine that, on the nested encoding of a code, input, and deadline, outputs $1$ followed by the decoded machine's output if it halts at that deadline, and outputs $0$ otherwise, in the displayed concrete quadratic time.

**Proof.** Choose the timed universal machine. The uniform computation result (`timed_computes`) gives its output as `timedAnswer` and its running time with coefficient equal to the startup bound, block bound, and fixed overhead. Expanding the startup bound yields the coefficient displayed in the theorem. If the decoded machine computes output $y$ at time $t$, the computation characterization (`computesInTime_iff`) says its run is halted then and has output $y$; hence `timedAnswer` is $1$ followed by $y$. If it computes no output at that time, the run cannot be halted: were it halted, its actual output would contradict the premise. Therefore `timedAnswer` is the one-bit output $0$. The simulation time is unchanged in both cases and is exactly the displayed coefficient times $(t+1)^2$.

**Key facts.** `Turing.timed_computes`, `Turing.FinTM.computesInTime_iff`.
