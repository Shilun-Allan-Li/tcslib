<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter07/QuadraticCircuitReduction.lean :: FABL.BooleanCircuit.circuitQuadraticInnerProof_join -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Recovery of the Inner Proof

**Claim.** When the extension and inner-proof assignments are joined, restricting the result to the inner-proof positions recovers the original inner-proof assignment.

**Proof.** Fix an inner-proof position $i$. Its position in the joined proof is obtained by adding the length of the extension to $i$, so it lies in the inner portion of the concatenation. By the definition of the joined proof, that position contains the value of the inner-proof assignment at $i$. Thus the two functions agree at every $i$, and the extracted inner proof equals the original assignment.
