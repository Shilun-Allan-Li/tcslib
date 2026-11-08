<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/ClassP/BinaryArith/Words.lean :: Complexity.BinArith.polyTimeComputable_countW -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Polynomial-Time Count Function

**Claim.** The function returning one $1$ for each iterate from $0$ through $|w|$ for which the iterated total second projection of $w$ is nonempty is polynomial-time computable.

**Proof.** Write $g$ for the total second projection. It is polynomial-time computable, and so is the emission function that returns the empty word when its input is empty and $[1]$ otherwise: the latter follows by testing emptiness and choosing between two constant outputs. At each index $i$, the summand in the definition of `countW` is precisely this emission function applied to $g^{[i]}(w)$. The iterate-length estimate `length_iterate_pairSndD_le` bounds the length of every such state by $|w|$, and hence by a linear polynomial in the input length. The polynomial-time theorem for emitting outputs along a polynomially bounded orbit (`polyTimeComputable_emitIter`) now gives the claimed function, with the range running from $0$ to $|w|$.

**Key facts.** `Complexity.polyTimeComputable_pairSndD`, `Complexity.polyTimeComputable_isNil`, `Complexity.polyTimeComputable_const`, `Complexity.polyTimeComputable_ite`, `Complexity.BinArith.length_iterate_pairSndD_le`, `Complexity.polyTimeComputable_emitIter`.
