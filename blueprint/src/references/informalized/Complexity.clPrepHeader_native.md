<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CookLevin/Hardness.lean :: Complexity.clPrepHeader_native -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Polynomial-Time Header Construction

**Claim.** For all natural parameters, the arithmetic preparation header function is computable in polynomial time.

**Proof.** Construct each component of the header using polynomial-time closure properties. The unary construction supplies the word of length $Q=C(|x|+1)^e$ (`Complexity.clNative_unary`); appending this to the identity output gives the word whose length is $m=|x|+Q$ (`Complexity.clNative_append`). Apply the unary construction again to obtain the word of length $T=c(A(m+1)^d+1)^2$, by composing the corresponding polynomial-time constructions (`Complexity.clNative_unary`, `Complexity.PolyTimeComputable.comp`). The length-to-binary conversion is linear-time, so composing it with the constructions of $Q$, $m$, and $T$ yields their binary representations (`Turing.FinTM.computesFunInTime_lengthBits`, `Complexity.clNative_linear`, `Complexity.PolyTimeComputable.comp`). Likewise, the all-false word of length $m$ is obtained by composing the linear-time fill construction with the construction of $m$ (`Complexity.clNative_fill`, `Complexity.PolyTimeComputable.comp`). Finally, repeatedly pair-encode the input and these components, using polynomial-time closure under pair encoding (`Complexity.clNative_pair`), to obtain exactly the stated header. The displayed definition agrees with this nested construction by the list-length and replication identities.

**Key facts.** `Complexity.clNative_unary`, `Complexity.clNative_append`, `Complexity.clNative_unary`, `Complexity.PolyTimeComputable.comp`, `Turing.FinTM.computesFunInTime_lengthBits`, `Complexity.clNative_linear`, `Complexity.PolyTimeComputable.comp`, `Complexity.clNative_fill`, `Complexity.PolyTimeComputable.comp`, `Complexity.clNative_pair`, `Complexity.polyTimeComputable_id`.
