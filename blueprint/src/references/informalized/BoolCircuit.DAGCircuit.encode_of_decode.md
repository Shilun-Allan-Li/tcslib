<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/DAGCircuitSatLang.lean :: BoolCircuit.DAGCircuit.encode_of_decode -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Encoding After Successful Decoding

**Claim.** If decoding a Boolean string $w$ succeeds and returns the circuit $C$, then encoding $C$ recovers $w$.

**Proof.** Unfold the decoder's successive option computations. A successful result supplies the decoded input count, gate list, output, and assembled circuit, together with the final successful check that this circuit's encoding equals $w$. The decoded result is precisely that assembled circuit; substituting it into the final check gives the desired equality.
