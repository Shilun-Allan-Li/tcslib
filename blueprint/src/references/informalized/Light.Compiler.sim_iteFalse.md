<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Programs/Light/Compiler/Simulation.lean :: Light.Compiler.sim_iteFalse -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Simulation of the False Conditional Branch

**Claim.** If the condition is safe but false, and the false-branch statement simulates execution from $\sigma$ to $\sigma'$ in $k$ steps, then the conditional simulates that execution in $\mathrm{cost}(c)+1+k$ steps.

**Proof.** Fix a starting configuration for the conditional. Its width bound gives bounds for the condition and both branches (`Stmt.width_ite_le_iff`), and the compiled-code decomposition identifies the condition test and the false-branch code (`codeAt_ite`). The test simulation, together with the fact that the condition fails, executes the test and reaches the false branch in at most its code size; it changes only scratch addresses (`Start.test`, `Decides.of_fails`). Since scratch addresses are writable, this change is within the permitted writable region (`scratch_subset_writable`). The relation is preserved across this test by `Rel.same`; the resulting configuration therefore satisfies the starting conditions for the false branch (`Start.sub`). Apply the assumed simulation of that branch to obtain its final memory, run, bound, and relation. Concatenate the test and branch runs and identify their endpoint with the position after the full conditional. The test takes at most the condition’s compiled size, which is bounded by its cost, and the branch takes at most the usual simulation allowance for $k$ language steps; the bound on the combined run follows from `add_le_stepsPerStep_mul`. Finally, combine the two memory-agreement facts, enlarging scratch agreement to writable-set agreement, using monotonicity and transitivity of agreement outside a set (`AgreeOutside.mono`, `AgreeOutside.trans`).

**Key facts.** `Light.Compiler.Stmt.width_ite_le_iff`, `Light.Compiler.codeAt_ite`, `Light.Compiler.Start.test`, `Light.Compiler.Decides.of_fails`, `Light.Compiler.scratch_subset_writable`, `Light.Compiler.Rel.same`, `Light.Compiler.Start.sub`, `Light.Compiler.add_le_stepsPerStep_mul`, `WordRAM.AgreeOutside.mono`, `WordRAM.AgreeOutside.trans`, `WordRAM.Steps.trans`, `WordRAM.Steps.cast_pos`.
