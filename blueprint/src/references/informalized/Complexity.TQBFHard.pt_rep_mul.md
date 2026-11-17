<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/ClassPSPACE/TQBFHardVerifier.lean :: Complexity.TQBFHard.pt_rep_mul -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Polynomial-Time Unary Replication

**Claim.** For every natural number $k$ and polynomial-time computable $g$, the function sending $y$ to a string of $k|g(y)|$ ones is polynomial-time computable.

**Proof.** Proceed by induction on $k$. When $k=0$, the output is the empty string, a constant function and hence polynomial-time computable (`polyTimeComputable_const`). For the successor step, assume a polynomial-time procedure outputs $k|g(y)|$ ones. The unary encoding of $|g(y)|$ is polynomial-time computable: first compute $g(y)$, then apply the polynomial-time unary-length function (`polyTimeComputable_unary`) by composition. Append this string to the induction-hypothesis output. The result remains polynomial-time computable by `PolyTimeComputable.append`, and its length is $k|g(y)|+|g(y)|=(k+1)|g(y)|$. Thus it is exactly the required unary replication for the successor.

**Key facts.** `Complexity.polyTimeComputable_const`, `Complexity.polyTimeComputable_unary`, `Complexity.PolyTimeComputable.comp`, `Complexity.PolyTimeComputable.append`.
