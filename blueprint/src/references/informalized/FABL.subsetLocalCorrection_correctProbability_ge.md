<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter07/DictatorTesting.lean :: FABL.subsetLocalCorrection_correctProbability_ge -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Local Correction Under Hamming Closeness

**Claim.** If $f$ is within relative Hamming distance $\delta$ of the parity indexed by $A$, then the local correction at the point corresponding to $S$ equals that parity’s value at the sign indicator of $S$ with probability at least $1-2\delta$.

**Proof.** First transfer the closeness assumption from the sign cube to the binary cube. The binary-to-sign coordinatewise bijection preserves the uniform average, and the parity on the sign cube transports to the binary parity (`binaryParitySign_transport_eq_parityFunction`). Therefore the relative Hamming distance between the encoded function and binary parity equals the original relative Hamming distance. The identity between disagreement probability and relative Hamming distance (`uniformProbability_ne_eq_relativeHammingDist`) makes this equality explicit, so the encoded function is within distance $\delta$ of binary parity. Apply the local-correction success bound (`localCorrection_successProbability`) to this binary function, the parity indexed by $A$, and the binary point corresponding to the subset indicator. This gives success probability at least $1-2\delta$. Finally, transport the parity value at that point back through the same binary-to-sign identity, yielding exactly the probability stated.

**Key facts.** `FABL.uniformProbability_ne_eq_relativeHammingDist`, `FABL.binaryParitySign_transport_eq_parityFunction`, `FABL.localCorrection_successProbability`.
