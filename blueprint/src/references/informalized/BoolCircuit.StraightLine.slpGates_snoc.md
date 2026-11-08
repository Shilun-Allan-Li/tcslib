<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/StraightLine.lean :: BoolCircuit.StraightLine.slpGates_snoc -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Appending a Statement's Gate

**Claim.** The gate list for $ss$ followed by $s$ is the gate list for $ss$ with the gate representing $s$ appended.

**Proof.** By definition, the gate list is the input-negation gates concatenated with the statement gates. Mapping the gate conversion over $ss++[s]$ gives the gates for $ss$ followed by the single gate for $s$; reassociating list concatenation yields the claimed equality.
