<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/ClassP/BinaryArith/Jacobi.lean :: Complexity.BinArith.polyTimeComputable_jacobiModAlg -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Polynomial-Time Jacobi Modular Algorithm

**Claim.** The function defined by the specified Jacobi modular algorithm is polynomial-time computable.

**Proof.** The algorithm is a composition of arithmetic operations on encoded Boolean words. First, encode the output of the Jacobi algorithm together with the decoded second input, then apply addition; encode that result with the constant word $[\mathsf{true}]$, then apply subtraction. Pair the result with the decoded second input and apply modular reduction. Each arithmetic operation is polynomial-time computable (`polyTimeComputable_add`, `polyTimeComputable_sub`, `polyTimeComputable_mod`); the decoded second input and constant word are polynomial-time computable (`polyTimeComputable_pairSndD`, `polyTimeComputable_const`), and pair encoding preserves polynomial-time computability (`PolyTimeComputable.pairEncode`). The Jacobi algorithm itself is polynomial-time computable (`polyTimeComputable_jacobiAlg`). Repeated closure under composition (`PolyTimeComputable.comp`) therefore proves the claim.

**Key facts.** `Complexity.BinArith.polyTimeComputable_jacobiAlg`, `Complexity.BinArith.polyTimeComputable_pairSndD`, `Complexity.polyTimeComputable_const`, `Complexity.PolyTimeComputable.pairEncode`, `Complexity.BinArith.polyTimeComputable_add`, `Complexity.BinArith.polyTimeComputable_sub`, `Complexity.BinArith.polyTimeComputable_mod`, `Complexity.PolyTimeComputable.comp`.
