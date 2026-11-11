<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/DAGCircuitSatLang.lean :: BoolCircuit.decodeList_encodeList -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Decoding an encoded list

**Claim.** Suppose each element code can be decoded, with any suffix preserved, to its element and that suffix. Then, with fuel strictly greater than the list length, decoding the encoding of the list followed by any suffix recovers the list and leaves the suffix unchanged.

**Proof.** Induct on the list, generalizing the fuel. For the empty list, the strict fuel bound guarantees positive fuel. Its encoding is the terminator bit, so the decoder returns the empty list and the untouched suffix. For a list $a::A$, the bound again gives positive fuel, say $m+1$. The element-decoding hypothesis applied to the suffix consisting of the encoded tail followed by the given remainder decodes the first element code to $(a,\operatorname{encode}(A)\mathbin{++}r)$. The list decoder then processes the encoded tail with fuel $m$. Since $|A|<m$, the induction hypothesis returns $(A,r)$. Combining these results gives $(a::A,r)$, as required.
