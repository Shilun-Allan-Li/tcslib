<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Robustness/ObliviousLedger.lean :: Complexity.obliviousCandidate_halts -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: low -->

# Halting of the candidate

**Claim.** Assuming the clock machine outputs the binary expansion of $T(|x|)$ within the prescribed time and $n\le T(n)$, the candidate reaches a halting state by the stated quadratic time bound on every input $x$.

**Proof.** Fix $x$. The clock-stage capture lemma (`clockStageCfg_captures`) provides a time $\tau\le b(T(|x|)+1)$ and a halted clock-machine configuration whose output is the binary expansion of $T(|x|)$, together with the schedule machine's configuration at that stage. The identity `budgetValue_bits` says that this binary output represents exactly $T(|x|)$. Its length is at most $b(T(|x|)+1)$, by the output-length bound for a machine run for a given number of steps (`MultiTapeTM.output_length_le`). Also, $|x|+1\le(a+1)(T(|x|)+1)$ follows from $|x|\le T(|x|)$. The setup lemma (`setupCfg_initializes`) then initializes the schedule's tapes and reaches the macro-check phase; the setup description (`clockStageCfg_setup`) identifies the captured configuration with the required starting form. From there, `setupCfg_finish` gives a halting configuration after the specified finishing time. Concatenating these run segments uses the run-addition identity (`runFrom_add`). The resulting total time is bounded by `obliviousLedger_bound`, using the bounds on $\tau$, the clock-output width, and the input length. Thus the schedule halts by the claimed quadratic bound. The proof-source’s final halting step follows this schedule-and-decoration route; the time bound is the one asserted in the claim.

**Key facts.** `Complexity.clockStageCfg_captures`, `Complexity.budgetValue_bits`, `Turing.FinTM.computesInTime_iff`, `Turing.MultiTapeTM.output_length_le`, `Turing.MultiTapeTM.runFrom_add`, `Complexity.clockStageCfg_setup`, `Complexity.setupCfg_initializes`, `Complexity.setupCfg_finish`, `Complexity.obliviousLedger_bound`.

**Caveat.** The supplied proof source for this lemma establishes halting of `obliviousSchedule`, whereas the formal statement asks for halting of `obliviousCandidate`. The route from the schedule result to the candidate result is not shown in this lemma’s proof source.
