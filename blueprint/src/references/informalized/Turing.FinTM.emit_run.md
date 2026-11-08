<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Simulation.lean :: Turing.FinTM.emit_run -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Partial Run of an Emission Chain

**Claim.** For every $t\le |w|$, the machine is in state $e(t)$ after $t$ steps and has output equal to the initial output followed by the first $t$ symbols of $w$.

**Proof.** Induct on $t$. At time zero, the state hypothesis gives state $e(0)$, and taking zero symbols leaves the output unchanged. For the successor step, the induction hypothesis puts the machine in state $e(t)$. The successor-run identity (`runFrom_succ_eq_step'`) expresses the next configuration as one transition from that state; the transition hypothesis makes this precisely the emission action at index $t$. Because $t<|w|$, this action outputs the $t$th symbol and moves to state $e(t+1)$. Appending that symbol to the previously emitted prefix gives the first $t+1$ symbols of $w$, as required.

**Key facts.** `Turing.MultiTapeTM.runFrom_succ_eq_step'`.
