<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/Randomized/ZeroPReduce.lean :: Randomized.PIT.shStep_pair -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Shift Step on a Paired Configuration

**Claim.** For any bit strings $M,w,out$, a shift step on their nested pairing either leaves it unchanged or returns a nested pairing with the same first component and with the sum of the lengths of the other two components bounded by $|w|+|out|+2|M|+8$.

**Proof.** The pairing decoder recovers the components of the input, by the facts that decoding an encoded pair returns its first and second components (`Complexity.pairFstD_pairEncode` and `Complexity.pairSndD_pairEncode`). If the decoded word meets the stopping condition, the shift step returns the input unchanged. Otherwise it produces the second branch of the claim. For its length bound, the transducer estimate says that the lengths of the head and remainder outputs together are at most the input length (`Randomized.PIT.length_uHead_add_uRest_le`). Apply this first to the body of $w$ and then to the remainder extracted from that body. The body has length at most $|w|$, since it is obtained by dropping four bits. Splitting into the variable, constant, and binary-operation cases in the definition of the step, these bounds control the retained word and the decoded gate arguments; the appended encoding contributes at most the stated additional $2|M|+8$. Combining the resulting natural-number inequalities gives the required bound.

**Key facts.** `Complexity.pairFstD_pairEncode`, `Complexity.pairSndD_pairEncode`, `Randomized.PIT.length_uHead_add_uRest_le`.
