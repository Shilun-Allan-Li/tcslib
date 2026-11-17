<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/SpaceComplexity/Logspace/QueryReshape.lean :: Complexity.dropIdx_query_overflow -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Overflow in a Dropped-Index Query

**Claim.** If the binary representation of the length of the encoding of $z$ with the binary representation of $r$ is shorter than the binary representation of $r$, then the dropped result has default bit $0$ at index $r$, and $r$ is at least its length.

**Proof.** The length of a natural number's binary representation is monotone. If the encoded length were at least $r$, monotonicity would contradict the assumed strict inequality between the bit lengths. Hence the encoded length is less than $r$. By the pair-encoding length formula, the encoded length is at least $|z|$; the length bound for dropping an index then gives $(\mathrm{dropIdx}\ z).\mathrm{length}\le r$. Thus index $r$ is out of range, so its default lookup is $0$, and the same inequality gives the second conclusion.

**Key facts.** `Complexity.LogProg.length_bits_mono`, `Turing.length_pairEncode`, `Complexity.dropIdx_length_le`.
