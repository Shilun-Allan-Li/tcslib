<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Universal.lean :: Turing.timed_universal -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Time-Bounded Universal Simulation with Timeout

**Claim.** For every effective machine-coding scheme, one finite-tape Boolean machine simulates each decoded machine on each input by a deadline: if it halts with output $y$ exactly at time $t$, the simulator outputs $1$ followed by $y$ on the nested time-and-code encoding in the stated quadratic time; if there is no output at exactly time $t$, it outputs $0$ in that same time.

**Proof.** Choose the timed universal machine. Its simulation result (`timed_computes`) says that on the nested encoding it runs for the stated quadratic time and produces `timedAnswer`: the output is $1$ followed by the decoded machine's output when that machine is halted at time $t$, and is the one-bit word $0$ otherwise. For the first implication, the computation characterization (`computesInTime_iff`) converts the hypothesis into the facts that the decoded run is halted and has output $y$. Substituting these facts into `timedAnswer` identifies the simulator's output as $1$ followed by $y$. For the timeout implication, if the decoded run were halted at time $t$, its actual output would witness a computation excluded by the hypothesis. Thus the run is live, and the other branch of `timedAnswer` gives output $0$. In both cases the running time is the one supplied by `timed_computes`.

**Key facts.** `Turing.timed_computes`, `Turing.FinTM.computesInTime_iff`.
