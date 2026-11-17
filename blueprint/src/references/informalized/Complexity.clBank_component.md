<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CookLevin/Hardness.lean :: Complexity.clBank_component -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# One Counter Component Reaches Its Result

**Claim.** After $2W+2$ steps, the single-tape counter machine is in return control with its head at cell zero, holding the binary representation of $n+1$ when selected and of $n$ otherwise; the input position and empty output are unchanged.

**Proof.** Split on the selection bit. If it is false, the machine starts in return control and remains idle, so the idle-run property gives the stated configuration after any number of steps (`Complexity.clCount_idle_run`). If it is true, it starts in carry control. The carry length is at most the binary word length, and therefore at most $W$ (`Complexity.clCountCarry_le`). The counter-run result says that after $2\,\mathrm{carry}(n.\mathrm{bits})+2$ steps the machine is in return control, its head is back at zero, and its tape holds the incremented word (`Complexity.clCount_run`); the incremented binary word represents $n+1$ (`Complexity.clCountInc_bits`). This duration is at most $2W+2$. The machine then remains idle for the remaining steps, again by the idle-run property. Decomposing the total run into these two successive intervals is justified by the run-addition law (`Turing.MultiTapeTM.runFrom_add`).

**Key facts.** `Complexity.clCountCarry_le`, `Turing.MultiTapeTM.runFrom_add`, `Complexity.clCount_run`, `Complexity.clCountInc_bits`, `Complexity.clCount_idle_run`.
