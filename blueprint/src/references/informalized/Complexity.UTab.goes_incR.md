<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/UniformTableauEmitter.lean :: Complexity.UTab.goes_incR -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# One-Step Register Increment

**Claim.** If the instruction at the current label increments register $r$ and proceeds to the specified next label, then from that label and input position the program reaches the next label in at most one step, with register $r$ increased by one, all other registers unchanged, the input position unchanged, and no additional output.

**Proof.** The one-step increment fact for counter programs (`goes_inc`) applies to the instruction hypothesis. It gives a run of at most one step to the next label, updating register $r$ to its old value plus one while preserving the input position and appending no output. The environment-update identity (`ER.update_f`) identifies this updated register function with the function encoded by setting register $r$ in $e$, which gives the claimed environment form.

**Key facts.** `Complexity.CounterProg.goes_inc`, `Complexity.UTab.ER.update_f`.
