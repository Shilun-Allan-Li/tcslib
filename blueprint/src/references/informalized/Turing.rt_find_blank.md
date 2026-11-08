<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Build/RecordTable.lean :: Turing.rt_find_blank -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Blank Input Transitions to Exit

**Claim.** From the halted body state with a blank under tape 0's head, the round machine reaches the exit state in two steps, and at every intervening positive time its state is neither distinguished read nor exit state.

**Proof.** The read-phase calculation (`rt_find_read`) gives the configuration after one step: the machine stores whether the scanned cell is occupied. Since that cell is blank, the stored value is false. The same calculation says that after the second step the redirect sends this false result to the exit phase, preserving the other configuration data. The only positive integer strictly between zero and two is one; at that time the state is the read phase with the stored value false, which differs from both the read phase with no stored value and the exit phase.

**Key facts.** `Turing.rt_find_read`.
