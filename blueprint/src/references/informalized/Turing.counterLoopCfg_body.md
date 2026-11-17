<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Build/CounterLoop.lean :: Turing.counterLoopCfg_body -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Recovering a Counter-Loop Configuration

**Claim.** Forming the body configuration from a counter-loop configuration and then rebuilding the counter-loop configuration with its original state and last tape recovers the original configuration.

**Proof.** The body configuration preserves the input position, output, and the contents and head positions of the first $k$ tapes. The embedding of those $k$ tapes into the first $k$ positions of $k+1$ tapes, together with the supplied contents and head position for the remaining tape, therefore reconstructs every tape component. The embedding-equality result (Turing.embedEmitCfg_eq) formalizes this componentwise comparison: its selected-tape conditions hold by the definition of the body configuration, and every tape outside the embedding is the last tape. Applying that equality and then restoring the original state gives the desired configuration equality.

**Key facts.** `Turing.embedEmitCfg_eq`.
