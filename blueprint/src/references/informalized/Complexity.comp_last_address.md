<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/SpaceComplexity/Logspace/QueryReshape.lean :: Complexity.comp_last_address -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Last Address in a Nested Encoding

**Claim.** When $b$ is nonempty, the bit at the stated address in $\langle\langle x,b\rangle,t\rangle$ equals the last bit of $b$, with the specified defaults.

**Proof.** Since $b$ is nonempty, its length is positive. The length formula for pair encodings (\texttt{length\_pairEncode}) rewrites the proposed address as $4|x|+4+2(|b|-1)$. The suffix-address identity (\texttt{comp\_suffix\_address}) therefore identifies the bit at this position with the bit of $b$ at index $|b|-1$. For a nonempty list, that indexed bit is its last bit; the default conventions agree, giving the claimed equality.

**Key facts.** `Turing.length_pairEncode`, `Complexity.comp_suffix_address`.
