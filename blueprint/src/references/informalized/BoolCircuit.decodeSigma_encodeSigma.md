<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/Encoding.lean :: BoolCircuit.decodeSigma_encodeSigma -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Recovery of Encoded Circuit Pairs

**Claim.** For every natural number $n$ and Boolean circuit tree $C$ on $n$ variables, decoding the encoding of $(n,C)$ returns that same pair.

**Proof.** Write the dependent pair as $(n,C)$. The natural-number prefix of its encoding is $	ext{encodeNat}(n)$ followed by $	ext{encodeCircuit}(C)$. The natural-number encoding recovery theorem (BoolCircuit.decodeNat_encodeNat) therefore decodes this prefix as $(n,	ext{encodeCircuit}(C))$. It remains to decode the circuit portion. The circuit reader recovery theorem (BoolCircuit.readCircuit_encodeCircuit) says that reading the encoding of $C$ with fuel at least its length returns $(C,[])$; here the fuel is exactly that length. Thus the decoder's final check compares the encoding of $(n,C)$ with itself and succeeds, returning $(n,C)$.

**Key facts.** `BoolCircuit.decodeNat_encodeNat`, `BoolCircuit.readCircuit_encodeCircuit`.
