<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/CodeSimulator.lean :: Turing.MachineFormat.guardBlock_short -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Guard block halts at the input boundary

**Claim.** If $|x|-j<b+1$, then after $|x|-j+1$ steps from position $j$ in phase zero, the guard machine is halted at position $|x|$, with output unchanged.

**Proof.** First run for $|x|-j$ steps. The bound $|x|-j<b+1$ permits the guard block run formula (Turing.MachineFormat.guardBlock_run), and those steps reach position $j+(|x|-j)=|x|$. One further step at the right blank cell halts without moving or changing the output (Turing.MachineFormat.guardBlock_blank). The run-after-a-successor formula (Turing.MultiTapeTM.runFrom_succ_eq_step') identifies these two stages with the stated total number of steps.

**Key facts.** `Turing.MultiTapeTM.runFrom_succ_eq_step'`, `Turing.MachineFormat.guardBlock_run`, `Turing.MachineFormat.guardBlock_blank`.
