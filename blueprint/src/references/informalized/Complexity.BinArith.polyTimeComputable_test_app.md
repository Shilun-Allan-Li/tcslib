<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/ClassP/BinaryArith/Loops.lean :: Complexity.BinArith.polyTimeComputable_test_app -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Composition with a Bit Output

**Claim.** If the bit-valued function $x\mapsto[p(x)]$ and the bit-string-valued function $g$ are polynomial-time computable, then $x\mapsto[p(g(x))]$ is polynomial-time computable.

**Proof.** Apply closure of polynomial-time computability under composition ( `Complexity.PolyTimeComputable.comp`) to the polynomial-time computable function $g$ and the polynomial-time computable function $y\mapsto[p(y)]$. Their composite sends $x$ to $[p(g(x))]$, as required.

**Key facts.** `Complexity.PolyTimeComputable.comp`.
