<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Finite.lean :: Turing.MultiTapeTM.runFrom_output_prepend -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Output prefixes are preserved throughout a run

**Claim.** Prefixing a configuration’s output by a finite string before a run has the same effect as prefixing the output after that run.

**Proof.** Let $f$ send each configuration to the configuration with its output prefixed by $p$. A single step commutes with this operation: the step rule appends the emitted output to the existing output, and list concatenation gives $p\mathbin{++}(x\mathbin{++}y)=(p\mathbin{++}x)\mathbin{++}y$ (`step_output_prepend`). The run-commutation principle (`runFrom_comm_of_step`) then extends this one-step identity to $t$ steps. Applying it to the initial configuration gives the stated equality.

**Key facts.** `Turing.MultiTapeTM.step_output_prepend`, `Turing.MultiTapeTM.runFrom_comm_of_step`.
