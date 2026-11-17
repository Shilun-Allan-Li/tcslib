<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/CircuitSatReductionMachineTapes.lean :: BoolCircuit.CktSatReduction.Emitter.apply_ctl -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Effect of a control action

**Claim.** A control action moves the input head as prescribed, leaves all work tapes and work-head positions unchanged, sets the successor state, and appends the optional output bit.

**Proof.** Unpack the configuration fields after applying the control action. Its state is $q$, its input head is moved from $p$ by $im$ with the prescribed clamping, and its output is $O$ followed by the optional bit. On each work tape the action specifies no write and zero head movement, so the tape and its head position remain the original ones. These are exactly the fields of the stated configuration.
