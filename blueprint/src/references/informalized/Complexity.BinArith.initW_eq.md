<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/ClassP/BinaryArith/DetMod.lean :: Complexity.BinArith.initW_eq -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Encoding the Initial Arithmetic State

**Claim.** For every bit string $z$, the initial word is the encoding of the arithmetic state whose rows are obtained by decoding the second component of $z$ into words and then entries, reducing each entry modulo the natural-number value of the first component of $z$. The state's remaining parameters are $1$, its number of rows, and $0$, and the state encoding uses the natural-number value of that first component as its parameter.

**Proof.** Rewrite the initial word and the state encoding using their definitions. The characterization of the count word identifies it with a string of true bits whose length is the number of decoded rows. The map-over-pairs result identifies the mapped word with the encoding of the list obtained by applying the row-modification procedure to each decoded word. Unfold that procedure and the row encoding: each decoded entry is converted to its natural-number value and reduced modulo the value of the first component. The fact that converting the canonical bit encoding of a natural number back to its value recovers that number simplifies each entry. The components now agree with the stated encoded state.

**Key facts.** `Complexity.BinArith.mapW_pairEncode`, `Complexity.BinArith.countW_eq`, `Complexity.LogProg.bitsVal_bits`.
