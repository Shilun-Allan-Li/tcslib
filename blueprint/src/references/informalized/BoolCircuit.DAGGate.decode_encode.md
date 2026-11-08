<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/DAGCircuitSatLang.lean :: BoolCircuit.DAGGate.decode_encode -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Decoding an encoded gate

**Claim.** For every Boolean gate $g$ and Boolean list $r$, decoding the encoding of $g$ followed by $r$ returns exactly $(g,r)$.

**Proof.** First, decoding the encoded gate kind followed by the remaining bits recovers the original kind and leaves the encoded argument list followed by $r$ (`GateKind.decode_encode`). Each natural-number argument is recovered together with its following remainder (`decodeNat_encodeNat`). The list decoding theorem then recovers the whole argument list and leaves precisely $r$ (`decodeList_encodeList`). Its fuel requirement is met because the list encoding has length at least the number of arguments plus one (`length_encodeList_ge`). Combining the recovered kind and arguments yields $g$, with remainder $r$.

**Key facts.** `BoolCircuit.GateKind.decode_encode`, `BoolCircuit.length_encodeList_ge`, `BoolCircuit.decodeList_encodeList`, `BoolCircuit.decodeNat_encodeNat`.
