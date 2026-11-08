<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/CircuitSatReductionMachine.lean :: BoolCircuit.CktSatReduction.Emitter.headsOf_update_zero -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Zero update of head positions

**Claim.** Updating the integer-valued head-position function at index $t$ to zero agrees with first updating the natural-valued function at $t$ to zero and then converting its values to integers.

**Proof.** This is the head-position update identity with $m=0$: the natural number zero casts to integer zero, so the two updates coincide.

**Key facts.** `BoolCircuit.CktSatReduction.Emitter.headsOf_update`.
