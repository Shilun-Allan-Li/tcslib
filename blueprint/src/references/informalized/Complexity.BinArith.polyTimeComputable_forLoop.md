<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/ClassP/BinaryArith/Loops.lean :: Complexity.BinArith.polyTimeComputable_forLoop -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Polynomial-Time Bounded Iteration

**Claim.** Under the stated polynomial bound on the lengths of iterates of $f$, iterating the specified state update $|S|+1$ times is polynomial-time computable.

**Proof.** First consider one update. It tests whether the first decoded component is empty; if so it returns the input unchanged. Otherwise it pairs the tail of that component with the image under $f$ of the second decoded component. The projections, emptiness test, tail operation and $f$ are polynomial-time computable, and composition and pairing assemble them into a polynomial-time update.

Now apply the polynomial-time iteration theorem to this update, starting from the identity initialization and running it $|S|+1$ times. It remains to give the required polynomial bound on every intermediate output length. Fix an input $S$ and a number of steps $i\leq |S|+1$. If decoding fails, the first decoded component is empty, so the update fixes $S$ and every iterate remains $S$, whose length is within the claimed bound. If decoding succeeds, write $S=\langle c,d\rangle$, using the fact that successful decoding recovers the original pair encoding. The iteration formula says that after $i$ steps the state is $\langle c\mathbin{\mathrm{drop}}i, f^{\min(i,|c|)}(d)\rangle$. The hypothesis bounds the length of the second component's iterate because $\min(i,|c|)\leq |c|$. The first component has length at most $|c|$, and the encoding-length formula expresses the output length as twice that first length plus two and the second length. Since both decoded component lengths are bounded by the input length, these estimates give a polynomial bound in $|S|$ (with the constants used in the iteration theorem). Thus the iterate is polynomial-time computable.

**Key facts.** `Complexity.polyTimeComputable_isNil`, `Complexity.polyTimeComputable_pairFstD`, `Complexity.polyTimeComputable_ite`, `Complexity.polyTimeComputable_id`, `Complexity.polyTimeComputable_tail`, `Complexity.polyTimeComputable_pairSndD`, `Complexity.PolyTimeComputable.comp`, `Complexity.PolyTimeComputable.pairEncode`, `Complexity.BinArith.polyTimeComputable_iterate`, `Complexity.BinArith.forStep_of_fst_nil`, `Turing.eq_pairEncode_of_pairDecode`, `Complexity.BinArith.iterate_forStep`, `Turing.length_pairEncode`.
