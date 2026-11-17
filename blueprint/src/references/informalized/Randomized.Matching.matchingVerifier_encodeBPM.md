<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/Randomized/Matching.lean :: Randomized.Matching.matchingVerifier_encodeBPM -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Verifier on Encoded Graphs

**Claim.** On the canonical encoding of a Boolean matrix $A$, the verifier accepts exactly when the random string is long enough and the sampled masked matrix over the Lovász prime field has nonzero determinant.

**Proof.** Unfold the verifier on the encoding of $A$. Its inferred size is the length of the first decoded component; pair encoding makes that component a string of $n$ true bits, so its length is $n$. The second decoded component is the adjacency word of $A$, and decoding that word back into a matrix recovers $A$ (`adjOfWord_adjWord`). Substituting these identities into the verifier's defining conjunction leaves exactly the stated length condition and determinant condition.

**Key facts.** `Randomized.Matching.adjOfWord_adjWord`.
