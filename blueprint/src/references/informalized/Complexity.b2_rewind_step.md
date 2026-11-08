<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/ClassNP/Nondeterminism.lean :: Complexity.b2_rewind_step -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# One Step of the Input Rewind

**Claim.** When $j<|x|$, one step from the loader configuration in state $1$ with input head at $j+1$, assembly buffer $x$, and assembly head at $|x|$ moves the input head to $j$ and preserves the rest of the configuration.

**Proof.** At input-head position $j+1$, the scanned symbol is $x[j]$ because $j<|x|$ (`Turing.inputSymbolInner`). In loader state $1$, the host takes its control action: it moves the input head left, changes no work-tape contents or heads, emits nothing, and remains in state $1$ (`Turing.FinTM.controlAction_apply`). A left move from position $j+1$ has position value $j$ (`Turing.FinTM.moveInputPos_neg_val`). Thus every component agrees with the loader configuration at position $j$.

**Key facts.** `Turing.inputSymbolInner`, `Turing.FinTM.controlAction_apply`, `Turing.FinTM.moveInputPos_neg_val`.
