<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/CircuitSatReductionSpec.lean :: BoolCircuit.CktSatReduction.Emitter.ES.vec_incTo -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Coordinate increment of an emitter state

**Claim.** For an emitter state with coordinate vector $v=(z,a,b)$ and any coordinate $t\in\{0,1,2\}$, advancing the state at coordinate $t$ replaces that coordinate by its value plus one and leaves the other coordinates unchanged.

**Proof.** Check the three possible coordinates $t$, and for each, compare the resulting state’s vector at each of the three coordinates. At the selected coordinate the definition of `incTo` adds one; at each of the other two it retains the original component. These are exactly the values of the function obtained by updating the original coordinate vector at $t$ with its value plus one.
