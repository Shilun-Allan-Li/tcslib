<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/ClassP/BinaryArith/Mul.lean :: Complexity.BinArith.polyTimeComputable_reverse -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Bit-String Reversal in Polynomial Time

**Claim.** The function sending each finite bit string to its reversal is polynomial-time computable.

**Proof.** Maintain the invariant that the current state encodes a pair $(u,v)$ with $u^{\mathrm{rev}}$ followed by $v$ equal to the reversal of the original word, and with $|u|+|v|$ equal to the original length. Start from the encoding of the original word and the empty word, which satisfies the invariant and is polynomial-time computable. The reverse-step transformation preserves the invariant: `revStep_pairEncode` says that it produces a new encoded pair with the same concatenated reversal and the same total length. It also says that whenever $u$ is nonempty, its length strictly decreases. The invariant is therefore preserved throughout every iterate (`iterate_invariant`), and the length formula for pair encodings gives a polynomial bound on the intermediate states. Thus `polyTimeComputable_iterate` shows that iterating the reverse step for the specified linear number of steps is polynomial-time computable. To see that this many steps suffices, use $|u|$ as a measure. It decreases whenever positive and, when it is zero, the reverse step fixes the state. The total length is the original word's length, so `iterate_measure_eq_zero` implies that the first component is empty by the end. The invariant then says the second component is the reversal of the input. Projecting it from the final encoding is polynomial-time computable, proving the claim.

**Key facts.** `Complexity.BinArith.revStep_pairEncode`, `Complexity.BinArith.iterate_invariant`, `Complexity.polyTimeComputable_id`, `Complexity.polyTimeComputable_const`, `Complexity.PolyTimeComputable.pairEncode`, `Turing.length_pairEncode`, `Complexity.BinArith.polyTimeComputable_iterate`, `Complexity.BinArith.iterate_measure_eq_zero`, `Complexity.pairFstD_pairEncode`, `Complexity.pairSndD_pairEncode`, `Complexity.PolyTimeComputable.comp`, `Complexity.polyTimeComputable_pairSndD`.
