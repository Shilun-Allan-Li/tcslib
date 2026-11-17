<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/ClassPSPACE/TQBFHardVerifier.lean :: Complexity.TQBFHard.pt_drop -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Polynomial-Time Prefix Truncation

**Claim.** If $o$ has a polynomial-time unary encoding and $S$ is polynomial-time computable, then the function $y\mapsto S(y).\mathrm{drop}(o(y))$ is polynomial-time computable.

**Proof.** Pair-encode the unary representation of $o(y)$ together with $S(y)$. Both components are polynomial-time computable, so their pair encoding is polynomial-time computable (`PolyTimeComputable.pairEncode`). The operation `PrefixByLength.drop` takes such an encoding and deletes from its second component as many bits as the first component has; it is polynomial-time computable by `polyTimeComputable_dropPrefixByLength`. Composing these operations gives the desired function: the length of a string of $o(y)$ ones is exactly $o(y)$, so the deletion count is the required offset, and the second component is $S(y)$.

**Key facts.** `Complexity.PolyTimeComputable.pairEncode`, `Complexity.polyTimeComputable_dropPrefixByLength`.
