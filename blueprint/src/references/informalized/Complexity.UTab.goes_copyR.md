<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/UniformTableauEmitterLayer.lean :: Complexity.UTab.goes_copyR -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Register Copy Loop

**Claim.** Starting in copy-loop mode with scratch zero, the program reaches the exit mode, adds the source value to the destination, preserves all other registers, the input position, and the output, and uses at most $7a+2$ steps, where $a$ is the initial source value.

**Proof.** The register environment of the given state is $e.f$. The environment-update identity says that updating this function at register $s.dst$ to the sum of its destination and source values is exactly the register function encoded by the updated environment (`ER.update_f`). Since $e.tmp=0$, the scratch register in $e.f$ is zero. The copy-loop theorem (`goes_copy`) therefore gives, for every output prefix, a run from phase zero to the exit with precisely that updated register function, unchanged input position and output, and the stated $7(e.f\ s.src)+2$ bound. Rewriting the target register function using the update identity gives the claimed environment form.

**Key facts.** `Complexity.UTab.ER.update_f`, `Complexity.UTab.goes_copy`.
