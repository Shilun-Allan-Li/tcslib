<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/LogspaceUniformScan.lean :: BoolCircuit.AdjScan.length_encodeList_cons -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Length of an Encoded Nonempty List

**Claim.** For a function $f$ assigning a bit list to each element, the encoding of $a::as$ has length $1+|f(a)|+|\operatorname{encode}(as)|$.

**Proof.** By definition, the encoding of $a::as$ consists of one leading marker bit, followed by $f(a)$ and then the encoding of $as$. The length of a concatenation is the sum of the lengths of its parts, so the total length is $1+|f(a)|+|\operatorname{encode}(as)|$.
