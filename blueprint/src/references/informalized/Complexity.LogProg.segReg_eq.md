<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/SpaceComplexity/Machines/Sim.lean :: Complexity.LogProg.segReg_eq -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Register of an Argument Segment

**Claim.** For a positive segment index no greater than the number of arguments, the assigned register is the argument register at index $s-1$.

**Proof.** Since $0<s\le |\mathrm{args}|$, the index $s-1$ is in range for the argument list. The definition of the segment register selects the list entry at that index; its fallback value is therefore unused. This gives the stated equality.
