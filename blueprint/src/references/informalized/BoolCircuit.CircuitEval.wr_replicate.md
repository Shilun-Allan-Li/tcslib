<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/CircuitEvalRun.lean :: BoolCircuit.CircuitEval.wr_replicate -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Extending a replicated tape

**Claim.** For every natural number r, updating the tape storing r consecutive true symbols from cell zero by setting cell r to true gives the tape storing r+1 consecutive true symbols from cell zero.

**Proof.** Writing true at the integer position corresponding to $r$ updates the tape at exactly that position. Split the list of $r+1$ repeated true symbols into the first $r$ symbols and one final true symbol (`List.replicate_succ'`). The tape for appending one symbol is obtained by updating the previous tape at its length (`Turing.FinTM.bufferTape_append`); the previous list has length $r$ (`List.length_replicate`). Thus this update is precisely the one at cell $r$, as claimed.

**Key facts.** `Turing.FinTM.bufferTape_append`.
