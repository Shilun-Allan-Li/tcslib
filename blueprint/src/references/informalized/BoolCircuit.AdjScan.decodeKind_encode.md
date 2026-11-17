<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/LogspaceUniformScan.lean :: BoolCircuit.AdjScan.decodeKind_encode -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Decoding an encoded gate kind

**Claim.** For any gate kind, decoding the two bits in its encoding returns that gate kind.

**Proof.** Check the three gate kinds. The encoding of AND is $(\mathrm{false},\mathrm{false})$, which decodes to AND; the encoding of OR is $(\mathrm{false},\mathrm{true})$, which decodes to OR; and the encoding of NOT is $(\mathrm{true},\mathrm{false})$, which decodes to NOT. In each case, the assumed equality of the encoding with $[b_1,b_2]$ identifies the two bits with the listed pair, so the decoding has the stated value.
