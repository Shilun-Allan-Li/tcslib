<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter07/PCPPConstructions.lean :: FABL.encodeBooleanFunctionProof_pcppProofFunction -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Recovery of an Indexed Boolean Function

**Claim.** Encoding an indexed Boolean function as a sign-valued function on the sign cube and then decoding it recovers the original indexed function exactly.

**Proof.** Fix an index $i$. Decoding the encoded function at $i$ evaluates that function at the sign vector corresponding to $i$, then applies the inverse Boolean-to-sign encoding. By definition, the encoded function at this vector reads the original function at the index assigned to the vector. Since the sign-cube indexing equivalence sends the vector corresponding to $i$ back to $i$, and the encoding equivalence followed by its inverse is the identity, the decoded value is the original value at $i$. This holds for every index, so the two indexed functions are equal.
