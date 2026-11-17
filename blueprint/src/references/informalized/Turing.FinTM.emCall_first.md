<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Build/Loop.lean :: Turing.FinTM.emCall_first -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# First exit of the call machine

**Claim.** Given a finite Boolean Turing machine that halts on argument $a$ with output $c$ after $T$ steps, the call machine has a first time $t$ when it enters its exit state. This time is positive and satisfies the stated bound; at that time its tapes and output have the required emit or install form.

**Proof.** First, the completion result (`Turing.FinTM.emCall_complete`) supplies a time within the stated bound at which the call machine is in the exit configuration with the required tape contents and output. Apply the first-entry principle for an absorbing stop state (`Turing.FinTM.emCall_first_entry`) to the predicate that a state is the exit state. Its hypothesis holds because every exit configuration is fixed by one step (`Turing.FinTM.emCall_exit_fixed`). The resulting time $t$ is at most the completion time, no earlier run state is an exit state, and the configuration at $t$ is the supplied exit configuration. Thus $t$ also satisfies the stated bound. Finally, $t$ cannot be zero: at time zero the machine is in its initial state, whereas the supplied configuration at $t$ has the distinct exit state. Therefore $t>0$, proving all the claims.

**Key facts.** `Turing.FinTM.emCall_complete`, `Turing.FinTM.emCall_exit_fixed`, `Turing.FinTM.emCall_first_entry`.
