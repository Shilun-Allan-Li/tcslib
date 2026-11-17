<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Build/StepClock.lean :: Turing.sc_body_step -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Clocked Body Step

**Claim.** A body-state step of the clocked machine performs the corresponding step of the underlying machine, preserves the additional tape and its head position, and changes to the decrement phase for a successor state or to the finish state if the underlying machine halts.

**Proof.** First, the embedding run theorem (`Turing.embedEmitTM_runFrom`) says that running the underlying machine after embedding its tapes into the larger tape collection agrees with embedding the underlying run. The layout identity (`Turing.sc_layout`) identifies this embedded configuration, with the additional tape and head supplied separately, as the clocked configuration. Specializing the run statement to one step and using the assumption that the underlying configuration is in state $s$ therefore identifies the embedded successor with the underlying one-step successor while retaining the additional tape contents and head position. In the clocked machine’s body state, its transition is precisely this embedded action with the successor relabeled: a successor state $s'$ becomes decrement state $(s',\mathrm{run})$, while a halting successor becomes $\mathrm{finish}$. Comparing the configuration components gives the claimed equality.

**Key facts.** `Turing.embedEmitTM_runFrom`, `Turing.sc_layout`.
