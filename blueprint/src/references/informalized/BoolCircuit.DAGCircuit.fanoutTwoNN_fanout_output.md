<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/StrictFanOut.lean :: BoolCircuit.DAGCircuit.fanoutTwoNN_fanout_output -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Zero fanout at the converted output

**Claim.** The output vertex of the fanout-reduced circuit has fanout zero.

**Proof.** The construction invariant states that every corresponding tap vertex has fanout zero. The converted circuit's output is the tap corresponding to the original output, which is a valid original vertex. Applying the invariant to that vertex gives the claim.

**Key facts.** `BoolCircuit.nnGates_inv`.
