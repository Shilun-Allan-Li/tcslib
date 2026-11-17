<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/ClassP/BinaryArith/Loops.lean :: Complexity.BinArith.polyTimeComputable_getW -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Polynomial-Time Loop Output

**Claim.** The function obtained by iterating the stated update on a bit string and then decoding the first component of the second component is polynomial-time computable.

**Proof.** First, the loop function that iterates the total second-component projection is polynomial-time computable. The loop theorem applies because each iterate of this projection has length at most the input length (`length_iterate_pairSndD_le`), and the pair encoding has length $2|x|+2+|y|$ (`length_pairEncode`); these give the required polynomial bound on intermediate lengths. The desired function is the composition of this loop with the second-component projection and then the first-component projection. Polynomial-time computability is preserved under composition (`PolyTimeComputable.comp`), and both projections are polynomial-time computable (`polyTimeComputable_pairSndD`, `polyTimeComputable_pairFstD`).

**Key facts.** `Complexity.BinArith.length_iterate_pairSndD_le`, `Turing.length_pairEncode`, `Complexity.BinArith.polyTimeComputable_forLoop`, `Complexity.polyTimeComputable_pairSndD`, `Complexity.PolyTimeComputable.comp`, `Complexity.polyTimeComputable_pairFstD`.
