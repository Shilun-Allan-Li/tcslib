<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/ClassP/BinaryArith/PrimeFind.lean :: Complexity.BinArith.polyTimeComputable_countLoop -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Polynomial-Time Counting Loop

**Claim.** The function that initializes the encoded pair with the empty word and an input word, then performs the specified counting update one more than the input length times, is polynomial-time computable.

**Proof.** First, the update `countStep` is polynomial-time computable. Its test asks whether the decoded second component is empty, a polynomial-time test; the two branches are respectively the identity and the construction that decodes the components, adds the one-bit word $[1]$ to the first component, drops the first bit of the second component, and re-encodes the pair. These operations are polynomial-time computable by closure under composition, encoding, and conditional choice, together with polynomial-time computability of addition and of the required projections and tail operation.

For the length bound on the iteration, use the invariant `CountInv z S`, which records that the current encoded state contains an accumulator and a remaining part of $z$, with the accumulator representing the number of bits already processed. The initial state `pairEncode [] z` satisfies this invariant: its accumulator is empty and its remaining part is $z$. The preservation fact `countInv_step` shows that each update preserves the invariant. Thus after any number $i$ of updates, `iterate_invariant` supplies the same description. The accumulator's value is at most $|z|$, so its canonical binary representation has length at most $|z|$; the remaining part also has length at most $|z|$. The pair-encoding length formula then gives a linear, hence polynomial, bound on every intermediate state. Applying the polynomial-time iteration theorem `polyTimeComputable_iterate` with the update, initialization, iteration count $|z|+1$, and this intermediate-length bound proves the result.

**Key facts.** `Complexity.BinArith.polyTimeComputable_add`, `Complexity.PolyTimeComputable.comp`, `Complexity.PolyTimeComputable.pairEncode`, `Complexity.polyTimeComputable_ite`, `Complexity.BinArith.countInv_step`, `Complexity.BinArith.iterate_invariant`, `Complexity.LogProg.length_bits_le`, `Turing.length_pairEncode`, `Complexity.BinArith.polyTimeComputable_iterate`.
