<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/ClassP/BinaryArith/Basic.lean :: Complexity.BinArith.polyTimeComputable_drop -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Polynomial-Time Prefix Deletion

**Claim.** For every natural number $i$, deleting the first $i$ bits of a bit string is polynomial-time computable.

**Proof.** Proceed by induction on $i$. When $i=0$, dropping zero bits is the identity function, which is polynomial-time computable. For the successor case, dropping $i+1$ bits is the same as first dropping $i$ bits and then dropping one more bit. By the induction hypothesis the first operation is polynomial-time computable, and deleting one bit is polynomial-time computable; closure under composition therefore gives the result for $i+1$.

**Key facts.** `Complexity.polyTimeComputable_id`, `Complexity.PolyTimeComputable.comp`, `Complexity.polyTimeComputable_tail`.
