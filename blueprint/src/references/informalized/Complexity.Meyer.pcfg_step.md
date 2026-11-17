<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/MeyerMachineParse.lean :: Complexity.Meyer.pcfg_step -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Step of the Encoded Simulator

**Claim.** For $1\le p\le |y|+1$, the next configuration from the encoded simulator configuration is the result of applying its transition rule to input symbol $y[p-1]?$, the three auxiliary tape symbols at the ends of their respective words, and blank symbols on every original work tape.

**Proof.** Unfold the buffered configuration and apply the step formula for configurations of this form (`acfg_step`). It expresses the next configuration as the action prescribed by the simulator transition rule, evaluated on the configuration's input symbol and scanned work-tape symbols. The input-symbol identification for the clipped position (`inputSymbol_fpos`) gives $y[p-1]?$. By the definition of the buffered tapes, the symbols scanned on the three auxiliary tapes are precisely their values at the word lengths, while the original work tapes are blank by construction. Substituting these values gives the claimed formula.

**Key facts.** `Complexity.Meyer.acfg_step`, `Complexity.Meyer.inputSymbol_fpos`.
