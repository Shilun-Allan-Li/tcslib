<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/SpaceComplexity/Logspace/QueryReshape.lean :: Complexity.dropIdx_length_le -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Length Bound for Dropping an Index

**Claim.** For every finite bit string $z$, the result of parsing the nested pair encoding and dropping the inner second component has length at most $|z|$.

**Proof.** Unfold the definition and split according to whether parsing $z$ succeeds, and then whether parsing the recovered inner string succeeds. If either parse fails, the result is empty and the bound is immediate. If both succeed, write the recovered data as $(u,b')$ and then $(w,b)$. The decoding equations show that $z$ is the pair encoding of $u,b'$, and $u$ is the pair encoding of $w,b$. Thus the output is the encoding of $w,b'$. The length formula for pair encoding gives its length as $2|w|+2+|b'|$, whereas $|z|=2|u|+2+|b'|$ and $|u|=2|w|+2+|b|$. Comparing these expressions yields the claimed bound.

**Key facts.** `Turing.eq_pairEncode_of_pairDecode`, `Turing.length_pairEncode`.
