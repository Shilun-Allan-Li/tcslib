<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/CircuitSatReductionMachineTapes.lean :: BoolCircuit.CktSatReduction.Emitter.step_some -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# One step from an active state

**Claim.** For a configuration with active state $q$, the next configuration is obtained by applying the action prescribed by the transition function at $q$, reading the input symbol and the symbols under the work-tape heads.

**Proof.** By definition, the machine’s step in an active state applies its transition function to the current state, the input symbol under the input head, and the symbols under the work-tape heads, then applies the resulting action to the configuration. This is exactly the asserted equality.
