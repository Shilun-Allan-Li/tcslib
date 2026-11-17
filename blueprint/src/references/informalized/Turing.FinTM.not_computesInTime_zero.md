<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Finite.lean :: Turing.FinTM.not_computesInTime_zero -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Impossibility of Zero-Step Computation

**Claim.** A finite Turing machine cannot compute an output in zero steps, regardless of the input or the specified space usage.

**Proof.** Suppose such a computation existed, and unpack its space witness. Its halting condition says that the machine's run from the initial configuration at time zero is in the halting state. But a zero-step run is just the initial configuration (`Turing.MultiTapeTM.runFrom_zero`), whose state is the machine's initial state, represented by `some q₀`. This is not the halting state `none`, a contradiction.

**Key facts.** `Turing.MultiTapeTM.runFrom_zero`.
