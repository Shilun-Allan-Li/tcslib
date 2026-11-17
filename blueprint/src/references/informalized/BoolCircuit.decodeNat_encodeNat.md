<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/UnaryCode.lean :: BoolCircuit.decodeNat_encodeNat -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Natural Number Encoding Recovery

**Claim.** For every natural number $k$ and Boolean-list suffix $r$, decoding the concatenation of $k$ true bits, one false bit, and $r$ returns $(k,r)$.

**Proof.** Induct on $k$. When $k=0$, the encoding consists of a single false bit, so the decoder returns the count $0$ and the remaining list $r$. For the successor case, the encoded list is a true bit followed by the encoding for $k$ and suffix $r$. By the induction hypothesis the decoder recovers $(k,r)$ from that tail; the leading true bit increments the count to $k+1$ and leaves $r$ unchanged.
