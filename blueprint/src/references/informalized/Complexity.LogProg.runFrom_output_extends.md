<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/SpaceComplexity/Machines/NARMCompile.lean :: Complexity.LogProg.runFrom_output_extends -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Output Extends the Initial Output

**Claim.** After $t$ steps, the output is the initial output followed by some finite word of symbols.

**Proof.** Proceed by induction on $t$. At time zero, take the appended word to be empty. For the successor step, suppose the output at time $t$ is the initial output followed by $u$. The run-successor identity says the next configuration is obtained by one machine step (`runFrom_succ_eq_step'`), and a single step appends the symbols emitted in that step to the current output (`step_output`). Thus the new output is the initial output followed by $u$ and then the step's emitted word. Associativity of concatenation combines these into one suffix, proving the induction step.

**Key facts.** `Turing.MultiTapeTM.runFrom_succ_eq_step'`, `Turing.MultiTapeTM.step_output`.
