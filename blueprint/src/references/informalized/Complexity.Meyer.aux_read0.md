<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/MeyerMachineSetup.lean :: Complexity.Meyer.aux_read0 -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# First Auxiliary Tape Read

**Claim.** When the work-tape values are extended by three auxiliary values, the value at the first auxiliary index is the first of those three values.

**Proof.** The extended function uses the original function on the first $k$ indices and the three-entry vector on the remaining indices. The index $\mathrm{Fin.natAdd}\ k\ 0$ is the first of those latter indices, so evaluating the three-entry vector there returns $a$.
