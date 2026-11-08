<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/ClassP/BinaryArith/Loops.lean :: Complexity.BinArith.polyTimeComputable_app -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Composition Preserves Polynomial Time

**Claim.** If $f$ and $g$ are polynomial-time computable functions on bit strings, then their composition $x\mapsto f(g(x))$ is polynomial-time computable.

**Proof.** Apply the closure of polynomial-time computability under composition (`Complexity.PolyTimeComputable.comp`) to the polynomial-time computation of $g$ followed by that of $f$. The resulting composite is $f\circ g$, which is the function claimed.

**Key facts.** `Complexity.PolyTimeComputable.comp`.
