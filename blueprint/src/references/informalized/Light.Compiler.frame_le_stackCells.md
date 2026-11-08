<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Programs/Light/Compiler/WholeProgram.lean :: Light.Compiler.frame_le_stackCells -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Frame Allocation Bound

**Claim.** For every program and limits record, the main frame size plus the program's frame size plus one is at most the number of stack cells allocated for that program under those limits.

**Proof.** Because the depth is a natural number, $\mathrm{depth}+1$ is positive. Thus $\mathrm{frameSize}(P)+1$ is at most $(\mathrm{frameSize}(P)+1)(\mathrm{depth}+1)$. Adding the main frame size to both sides and using the definition of the stack-cell count gives the stated bound.
