<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Build/CounterLoop.lean :: Turing.counter_decrement_run -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Decrement Run by Complementation

**Claim.** Running the decrement machine for $t$ steps from $d$ gives the same configuration as complementing the work-tape symbols in $d$, running the increment machine for $t$ steps, and complementing the result.

**Proof.** The decrement machine is the increment machine with its work-symbol interpretation transported through Boolean complementation. The run-transport theorem says that transporting a machine’s work symbols transports every finite run in the same way (Turing.MultiTapeTM.mapWorkSymbols_runFrom). Apply it to the increment machine and the complemented starting configuration. The resulting configuration has the work symbols complemented twice; complementation twice is the identity (Turing.counter_complement_twice), yielding the claimed equality.

**Key facts.** `Turing.MultiTapeTM.mapWorkSymbols_runFrom`, `Turing.counter_complement_twice`.
