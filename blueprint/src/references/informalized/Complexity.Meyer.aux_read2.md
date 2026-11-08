<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/MeyerMachineSetup.lean :: Complexity.Meyer.aux_read2 -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Third Auxiliary Read

**Claim.** After extending the work-tape assignment by the three auxiliary values $a,b,c$, the value at the third auxiliary index is $c$.

**Proof.** The extension agrees with $f$ on the work-tape indices and uses the three-entry vector $(a,b,c)$ on the added indices. The index $	ext{natAdd}(k,2)$ selects the last entry of that vector, so its value is $c$.
