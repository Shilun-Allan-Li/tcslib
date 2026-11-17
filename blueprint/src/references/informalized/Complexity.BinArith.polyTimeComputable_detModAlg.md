<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/ClassP/BinaryArith/DetMod.lean :: Complexity.BinArith.polyTimeComputable_detModAlg -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Polynomial-Time Determinant Algorithm

**Claim.** The algorithm returning the empty string when the decoded first component represents a number less than $2$, and otherwise returning the third component after the prescribed number of determinant-state updates, is polynomial-time computable.

**Proof.** First construct the initialization `initW` in polynomial time. Normalize the decoded first component to its canonical binary representation, build the encoded initial rows using the polynomial-time map operation and the entry-modulus routine, and assemble the remaining fields using the counting loop and constant outputs. These components are polynomial-time computable by the stated closure properties.

The initial state has the mathematical form given by `initW_eq`: it encodes the parameter $p=\operatorname{bitsVal}(\operatorname{pairFstD}(z))$ together with the initial rows and counters. The invariant `LInv` holds for this state. Its row-length clauses follow because decoded words have length no greater than the word from which they are decoded (`length_decWords_le` and `length_le_of_mem_decWords`), and the input's decoded second component has length at most $|z|$. Its entry-size clause follows from `bitsVal_lt_two_pow` and the fact that each entry is reduced modulo $p$. The other initial bounds are immediate from the displayed parameters.

Each determinant-state update preserves `LInv`: `lInv_step` applies because $p\le p+2^{|z|}+2$. Thus `iterate_invariant` gives the invariant at every intermediate state. The representation identity `iterate_detWStep_encState` identifies the encoded iteration with the corresponding iteration of the abstract determinant-state transition. The size estimate `length_encState_le` then bounds each encoded state by $64(|z|+1)^3$. Applying `polyTimeComputable_iterate` to the polynomial-time update `detWStep` and initialization proves that the required fixed-iteration state is polynomial-time computable.

Finally, the condition that the decoded first component has value less than $2$ is polynomial-time computable by comparing it with the canonical binary encoding of $2$. A polynomial-time conditional returns the empty word in that case, and otherwise takes the third component of the iterated state. Both branches are polynomial-time computable, so the conditional closure property proves the result.

**Key facts.** `Complexity.LogProg.bitsVal_bits`, `Complexity.BinArith.polyTimeComputable_normBits`, `Complexity.BinArith.polyTimeComputable_mod`, `Complexity.BinArith.polyTimeComputable_mapW`, `Complexity.BinArith.polyTimeComputable_countW`, `Complexity.BinArith.polyTimeComputable_iterate`, `Complexity.BinArith.initW_eq`, `Complexity.BinArith.length_decWords_le`, `Complexity.BinArith.length_le_of_mem_decWords`, `Complexity.BinArith.length_pairSndD_le`, `Complexity.LogProg.bitsVal_lt_two_pow`, `Complexity.BinArith.lInv_step`, `Complexity.BinArith.iterate_invariant`, `Complexity.BinArith.iterate_detWStep_encState`, `Complexity.BinArith.length_encState_le`, `Complexity.BinArith.polyTimeComputable_detWStep`, `Complexity.BinArith.polyTimeComputable_lt`, `Complexity.BinArith.polyTimeComputable_slot3`, `Complexity.polyTimeComputable_ite`.
