<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Build/Catalog.lean :: Turing.FinTM.f2_loop_output_length_le -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Output Length Growth Bound

**Claim.** After $t$ steps, the output length is at most the initial output length plus $t$.

**Proof.** In one step, the machine appends the transition's optional output symbol to the existing output. By the output formula for a step (`Turing.MultiTapeTM.step_output`), the new length is therefore the old length plus either zero or one, and hence is at most the old length plus one. Induct on the number of steps. At zero steps the output is unchanged. For the successor case, the run after $t+1$ steps is one step applied to the run after $t$ steps (`Turing.MultiTapeTM.runFrom_succ_eq_step'`). Apply the one-step bound and then the induction hypothesis to obtain the claimed bound.

**Key facts.** `Turing.MultiTapeTM.step_output`, `Turing.MultiTapeTM.runFrom_succ_eq_step'`.
