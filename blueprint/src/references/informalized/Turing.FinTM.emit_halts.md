<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Simulation.lean :: Turing.FinTM.emit_halts -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Halting After an Emission Chain

**Claim.** If every indexed state transitions according to the emission action for the word, then a configuration in state $e(0)$ halts after exactly $|w|+1$ steps with its original output followed by $w$.

**Proof.** The partial emission-chain result (`emit_run`) gives the state and output after $|w|$ steps: the machine is in state $e(|w|)$ and has appended the first $|w|$ symbols of $w$, hence all of $w$. Take one more step. The successor state is the terminal state and the emission action contributes no further output at the final index. Thus the machine has halted and its output is the original output followed by $w$.

**Key facts.** `Turing.FinTM.emit_run`, `Turing.MultiTapeTM.runFrom_succ_eq_step'`.
