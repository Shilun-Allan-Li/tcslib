<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Robustness/ObliviousCandidate.lean :: Complexity.clockStageCfg_captures -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Capturing a Halted Clock Configuration

**Claim.** For each Boolean input $x$, the schedule machine reaches after $[?1m\tau+1[?1m$ steps the clock-stage configuration associated with a halted configuration of $W$ that outputs $(T(|x|)).bits$, for some $[?1m\tau\le b(T(|x|)+1)[?1m$.

**Proof.** The masked machine, which presents false whenever $W$ reads a nonblank input symbol, still computes $(T(|x|)).bits$ within the stated time bound (the preservation result `maskedClock_computes`). Thus it halts by that bound. Choose its first halting time $\tau$; the existence of a halting time gives such a least time, and the least-time property gives $\tau\le b(T(|x|)+1)$. Let $c$ be its configuration at time $\tau$. Then $c$ is halted. The computation characterization `computesInTime_iff` identifies the output of a computation with the output field of its terminal configuration, and uniqueness of outputs across computations (`ComputesInTime.output_unique`) shows that $c.output=(T(|x|)).bits$. Finally, every configuration of the masked computation up to time $\tau$ is nonhalting before time $\tau$. The run correspondence through the clock phase (`clockStageCfg_run`), applied at $t=\tau$, therefore identifies the schedule machine's configuration after $\tau+1$ steps with the clock-stage configuration associated with $c$.

**Key facts.** `Complexity.maskedClock_computes`, `Turing.FinTM.computesInTime_iff`, `Turing.FinTM.ComputesInTime.output_unique`, `Complexity.clockStageCfg_run`.
