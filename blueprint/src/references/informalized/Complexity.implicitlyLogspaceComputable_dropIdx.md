<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/SpaceComplexity/Logspace/QueryReshape.lean :: Complexity.implicitlyLogspaceComputable_dropIdx -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Logspace Computability of Index Deletion

**Claim.** The function that parses an input as an encoded pair $(u,b')$, then parses $u$ as $(w,b'')$ and outputs the encoding of $(w,b')$, returning the empty string if either parse fails, is implicitly logspace computable.

**Proof.** The length bound follows from the fact that deleting the inner index never increases length (`dropIdx_length_le`): the output length is at most the input length, hence at most $1\cdot(|x|+1)^1$. The two required index languages are precisely the output-bit language and output-length language for this function. The supplied logspace result for the deletion procedure (`drop_mem`) establishes membership for both modes: mode false expresses whether the indicated output bit is $1$, and mode true expresses whether the index is below the output length.

**Key facts.** `Complexity.dropIdx_length_le`, `Complexity.drop_mem`.
