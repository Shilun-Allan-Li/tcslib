<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/Encoding.lean :: BoolCircuit.circuitEncoding_decode -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Circuit Encoding and Decoding

**Claim.** For every finite variable bound, decoding the circuit encoding agrees with first decoding the variable bound and then reading a circuit, with acceptance only when re-encoding recovers the input bit string.

**Proof.** The two decoding procedures are definitionally the same: both first decode the unary variable bound, then read a circuit from the remaining bits using the remaining list length as fuel, require that no bits remain, and accept only if encoding the resulting bound-and-circuit pair reproduces the original string. Thus their outputs agree for every input.
