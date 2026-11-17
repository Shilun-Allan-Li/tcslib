<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/CodeSimulator.lean :: Turing.MachineFormat.guardBlock_run -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Guard block run advances by the requested length

**Claim.** After $u$ steps from position $j$ in phase zero, where $u\le b+1$ and $j+u\le |x|$, the guard machine is at position $j+u$ in phase $u$ modulo $b+1$, with output unchanged.

**Proof.** Induct on $u$. At zero steps the configuration is unchanged. For the successor step, the bounds imply that the current phase index is below $b+1$ and the current position is strictly before the end of the input. Thus one interior step advances the head by one cell and the phase from $u$ to $u+1$, leaving the output unchanged (Turing.MachineFormat.guardBlock_step). The induction hypothesis gives the configuration before that step, and the run-after-a-successor formula (Turing.MultiTapeTM.runFrom_succ_eq_step') relates it to the configuration after the additional step. This proves the claimed position and phase.

**Key facts.** `Turing.MachineFormat.guardBlock_step`, `Turing.MultiTapeTM.runFrom_succ_eq_step'`.
