<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Finite.lean :: Turing.MultiTapeTM.output_length_le -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Output Length Is Bounded by Time

**Claim.** After $t$ steps from the initial configuration, the output word has length at most $t$.

**Proof.** Use induction on $t$. At time zero the initial output is empty, so the bound holds. For the successor time, the run after $t+1$ steps is one step from the configuration at time $t$ (`Turing.MultiTapeTM.runFrom_succ_eq_step'`). A step appends the list form of the output symbol prescribed at that configuration (`Turing.MultiTapeTM.step_output`). That list has length at most one, whether the symbol is absent or present. Hence the new output length is at most the old length plus one, which is at most $t+1$ by the induction hypothesis.

**Key facts.** `Turing.MultiTapeTM.runFrom_succ_eq_step'`, `Turing.MultiTapeTM.step_output`.
