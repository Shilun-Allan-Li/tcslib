<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/UniformTableauEmitter.lean :: Complexity.UTab.goes_decR -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# One-Step Register Decrement

**Claim.** If the instruction at the current label decrements register $r$ and jumps to the specified next label, then for every output prefix the program reaches that label in at most one step, with register $r$ reduced by one (and hence still zero if it was zero), all other registers unchanged, and the input position and output unchanged.

**Proof.** The one-step decrement fact for counter programs (`goes_dec`) applies directly to the instruction hypothesis: it produces the next label and the register function obtained by updating register $r$ to its old value minus one, within one step, without changing the input position or appending output. The environment-update identity (`ER.update_f`) identifies that updated function with the function encoded by setting register $r$ in $e$. This yields the stated conclusion for every output prefix.

**Key facts.** `Complexity.CounterProg.goes_dec`, `Complexity.UTab.ER.update_f`.
