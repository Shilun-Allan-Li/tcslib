<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/MeyerTableau.lean :: Complexity.Meyer.step_eq -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Transition Step from a Nonhalting Configuration

**Claim.** If a configuration has state $q$, its next step is the result of applying the transition action prescribed at $q$ to the symbols currently read on the input and work tapes.

**Proof.** The hypothesis that the state is $q$ selects the nonhalting branch in the definition of a machine step. The input symbol read by the configuration equals its input-tape read at displacement zero (`Complexity.Meyer.inputSymbol_eq_xhat`), and each work-tape symbol equals the corresponding read at displacement zero (`Complexity.Meyer.workTapeSymbols_eq_RW`). Together these are exactly the read data packaged as $\mathrm{reads}(c)$. Substituting them into the selected transition action gives the stated step equation.

**Key facts.** `Complexity.Meyer.inputSymbol_eq_xhat`, `Complexity.Meyer.workTapeSymbols_eq_RW`.
