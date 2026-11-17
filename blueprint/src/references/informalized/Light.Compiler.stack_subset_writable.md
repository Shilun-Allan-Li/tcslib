<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Programs/Light/Compiler/Cells.lean :: Light.Compiler.stack_subset_writable -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Stack Cells Are Writable

**Claim.** For any size configuration $Z$ and stack base $q$, every address in the stack region from $q$ up to, but not including, the stack capacity of $Z$ is writable at base $q$.

**Proof.** By definition, the writable addresses include the stack region as one of the sets in a union. Thus every member of `Stack q Z.Q` belongs to `Writable Z q`.
