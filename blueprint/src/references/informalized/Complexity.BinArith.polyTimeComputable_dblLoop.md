<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/ClassP/BinaryArith/PrimeFind.lean :: Complexity.BinArith.polyTimeComputable_dblLoop -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Polynomial-Time Doubling Loop

**Claim.** The function obtained by applying the doubling step $2(|z|+1)$ times to the specified encoded initial pair is polynomial-time computable.

**Proof.** The step `dblStep` is polynomial-time computable: its comparison is polynomial-time computable, and its two branches are the identity and the encoded pair made from a prefixed first projection and the second projection. The initial state is polynomial-time computable as well, by composing the polynomial-time counting loop with the projection and then forming the required encodings and prefix.

To bound the iterates, the invariant `DblInv z.length` holds initially. Indeed, `countLoop_eq` identifies the counting-loop output as the encoding of the binary expansion of $|z|$ and the empty word, which gives the initial invariant with counter value zero. The preservation statement `dblInv_step` and induction on the number of updates (`iterate_invariant`) keep this invariant throughout the run. It bounds the first component in terms of the binary length of $|z|$ and the quantity $\operatorname{clog}_2(2|z|)$. The bounds `lovaszBits_le` and `length_bits_le` show these quantities are at most linear in $|z|$. The pair-encoding length formula therefore bounds every intermediate state by a polynomial in $|z|$. The polynomial-time iteration theorem `polyTimeComputable_iterate`, with $2(|z|+1)$ updates, proves the claim.

**Key facts.** `Complexity.BinArith.polyTimeComputable_lt`, `Complexity.BinArith.polyTimeComputable_cons`, `Complexity.PolyTimeComputable.pairEncode`, `Complexity.polyTimeComputable_ite`, `Complexity.BinArith.polyTimeComputable_countLoop`, `Complexity.BinArith.countLoop_eq`, `Complexity.BinArith.dblInv_step`, `Complexity.BinArith.iterate_invariant`, `Complexity.BinArith.lovaszBits_le`, `Complexity.LogProg.length_bits_le`, `Turing.length_pairEncode`, `Complexity.BinArith.polyTimeComputable_iterate`.
