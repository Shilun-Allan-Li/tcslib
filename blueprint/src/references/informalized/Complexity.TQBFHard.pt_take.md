<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/ClassPSPACE/TQBFHardVerifier.lean :: Complexity.TQBFHard.pt_take -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Polynomial-Time Prefix Truncation

**Claim.** If the unary string of length $o(y)$ and the string $S(y)$ are each polynomial-time computable, then the prefix of $S(y)$ of length $o(y)$ is polynomial-time computable.

**Proof.** Pair the two polynomial-time outputs: the unary string of length $o(y)$ and $S(y)$. The pairing construction preserves polynomial-time computability (`PolyTimeComputable.pairEncode`). Apply the polynomial-time operation that, on a paired input, takes from its second component a prefix whose length is the length of its first component (`polyTimeComputable_takePrefixByLength`). Since the first component is unary of length $o(y)$, this prefix has length $o(y)$, as required. Polynomial-time composition then establishes the claim (`PolyTimeComputable.comp`).

**Key facts.** `Complexity.PolyTimeComputable.pairEncode`, `Complexity.polyTimeComputable_takePrefixByLength`, `Complexity.PolyTimeComputable.comp`.
