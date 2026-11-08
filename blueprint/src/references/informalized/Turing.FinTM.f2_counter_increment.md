<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Build/Catalog.lean :: Turing.FinTM.f2_counter_increment -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Counter Increment and Rewind

**Claim.** For every Boolean list $x$, every $i<|x|$, and every Boolean list $bs$, running the machine for $2\,\mathrm{carry}(bs)+2$ steps from the stated state-$0$ configuration reaches state $0$ with input head at $i+2$, work-tape head at $0$, incremented tape, and empty output.

**Proof.** First, after $\mathrm{carry}(bs)+1$ steps, the machine is in state $2$, with the tape changed to the binary increment of $bs$ and the head positioned at $\mathrm{carry}(bs)-1$ (`f2_counter_carry`). To obtain this carry-phase run, the proof compares the first state-$0$ transition with the corresponding state-$1$ transition (`f2_counter_start`), then uses the one-step run identities to enter and execute the carry procedure. Now split the full duration as two blocks of $\mathrm{carry}(bs)+1$ steps, using `runFrom_add`. The first block is the carry phase just described; the second rewinds the work-tape head to zero while preserving the incremented tape and input position (`f2_counter_rewind`), using the bound that the carry does not exceed the incremented word's length (`f2_counterInc_length`).

**Key facts.** `Turing.FinTM.f2_counter_carry`, `Turing.FinTM.f2_counter_start`, `Turing.MultiTapeTM.runFrom_add`, `Turing.FinTM.f2_counter_rewind`, `Turing.FinTM.f2_counterInc_length`, `Turing.MultiTapeTM.runFrom_succ_eq_step`.
