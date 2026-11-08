<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/ClassP/BinaryArith/DetMod.lean :: Complexity.BinArith.polyTimeComputable_entryW -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Polynomial-Time Binary Arithmetic Function

**Claim.** The function that computes the specified binary arithmetic expression from the parsed components of a bit string is polynomial-time computable.

**Proof.** Extract the first component of the first decoded pair, and also the first component of the second decoded pair. The pair-projection results and composition make both extractions polynomial-time computable. The other required inputs are obtained by the slot selectors: the first component of the input's second decoded pair and the second component of its second decoded pair.

Using the extracted components, first multiply the two values represented by the latter pair, then reduce that product modulo the designated divisor. Next add the two values from the first components of the decoded pairs, and subtract the remainder just computed. Finally reduce this difference modulo the same divisor. At each stage, encode the operands as a pair and apply the polynomial-time multiplication, modulo, addition, or subtraction function as appropriate; pair encoding preserves polynomial-time computability, as does composition. The resulting nested calculation is exactly the stated function, so it is polynomial-time computable.

**Key facts.** `Complexity.polyTimeComputable_pairFstD`, `Complexity.PolyTimeComputable.comp`, `Complexity.polyTimeComputable_pairSndD`, `Complexity.BinArith.polyTimeComputable_slot2`, `Complexity.BinArith.polyTimeComputable_slot3`, `Complexity.PolyTimeComputable.pairEncode`, `Complexity.BinArith.polyTimeComputable_mul`, `Complexity.BinArith.polyTimeComputable_mod`, `Complexity.BinArith.polyTimeComputable_add`, `Complexity.BinArith.polyTimeComputable_sub`.
