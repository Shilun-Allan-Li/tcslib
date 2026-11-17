<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/Encoding.lean :: BoolCircuit.circuitEncoding_encode -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Circuit Encoding Map

**Claim.** The encoding map for pairs consisting of a natural-number variable bound and a Boolean circuit tree concatenates the unary encoding of the bound with the encoding of the circuit tree.

**Proof.** Unfolding the encoding map on a bound-and-circuit pair gives precisely the unary encoding of the bound followed by the circuit encoding. This is the defining formula for the stated concatenation map, so the two maps agree.
