<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Simulation.lean :: Turing.FinTM.timed_rewind -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Bounded Rewind to the Input Start

**Claim.** Under the specified transitions from $r$ and $s$, a configuration in state $r$ can reach state $d$ at input-head position $1$ in at most $p+2$ steps, where $p$ is its initial input-head position.

**Proof.** The first transition, from state $r$, moves the input head left once and enters $s$, changing no other part of the configuration. A left move changes the position from $p$ to $p-1$ (`moveInputPos_neg_val`); the position is therefore within the input region. From state $s$, the machine continues moving left while it scans input symbols, and on the blank at the left boundary it moves right and enters $d$. The rewind fact (`rewind_scan`) says that from position $p-1$ this takes exactly $(p-1)+1$ further steps and ends at position $1$, with all other configuration fields unchanged. Hence the total number of steps is $1+((p-1)+1)=p+1$, which is at most $p+2$. The initial step calculation uses the control-action behavior (`controlAction_apply`), and the run is split into consecutive segments using `runFrom_add`.

**Key facts.** `Turing.FinTM.controlAction_apply`, `Turing.FinTM.moveInputPos_neg_val`, `Turing.FinTM.rewind_scan`, `Turing.MultiTapeTM.runFrom_add`.
