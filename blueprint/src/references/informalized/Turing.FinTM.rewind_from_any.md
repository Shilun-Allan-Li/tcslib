<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Simulation.lean :: Turing.FinTM.rewind_from_any -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Rewind to the left boundary

**Claim.** From every configuration in state $r$, there is a finite number of steps after which the machine is in state $d$ at input-head position $1$, with all other configuration components unchanged.

**Proof.** First take one step from the configuration in state $r$. The prescribed action moves the input head left, changes the state to $s$, and leaves all other components unchanged (`controlAction_apply`). Call the resulting configuration $c$. Its input-head position is at most the input length: the left move reduces the position by one (`moveInputPos_neg_val`), and the original position lies in the allowed range. Now apply the scanning behavior of state $s$: as long as an input symbol is present, it keeps moving left in state $s$; upon reaching the blank at the left boundary, it moves right and enters state $d$. The scan lemma formalizes this process, showing that from $c$ it reaches position $1$ after $c$'s position plus one steps, without changing any other component (`rewind_scan`). The run-addition law composes this scan with the initial step (`runFrom_add`), giving the claimed total number of steps and final configuration.

**Key facts.** `Turing.FinTM.controlAction_apply`, `Turing.FinTM.moveInputPos_neg_val`, `Turing.FinTM.rewind_scan`, `Turing.MultiTapeTM.runFrom_add`.
