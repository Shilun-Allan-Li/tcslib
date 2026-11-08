<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/CodeSimulator.lean :: Turing.MachineFormat.canonBoolPop_run -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# One-Step Boolean Tape Pop

**Claim.** Starting with the machine in its initial state and with $[b]$ on tape $0$ and all other work tapes empty, one step leaves the machine in state $b$ with every work tape empty, while the input head, work-tape heads, and output remain at their initial values.

**Proof.** A run of one step is the successor run after a run of zero steps (`Turing.MultiTapeTM.runFrom_succ_eq_step`), and a zero-step run is the original configuration (`Turing.MultiTapeTM.runFrom_zero`). Thus it suffices to evaluate one transition and its effect on the initial configuration. In the initial state, the transition reads tape $0$; its contents are the singleton $[b]$, so the defaulted first symbol is $b$. The transition erases the scanned cell and leaves its head in place, sets the state to $b$, and makes no input-head move or output. The singleton tape has only that cell, so erasing it leaves the empty tape; every other tape is untouched and already empty. Hence all tape contents are empty, all head positions and the input position are unchanged, and the output stays empty.

**Key facts.** `Turing.MultiTapeTM.runFrom_succ_eq_step`, `Turing.MultiTapeTM.runFrom_zero`.
