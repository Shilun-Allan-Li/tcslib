<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/Diagonalization/NotTimeConstructible.lean :: Complexity.ntc_primrec_rank -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Primitive Recursiveness of Rank

**Claim.** For a bit string $s$, let $r(s)$ be obtained by appending a $1$ to $s$, interpreting the result in least-significant-bit-first binary, and subtracting $1$. The function $s\mapsto r(s)$ is primitive recursive.

**Proof.** Append the constant bit $1$ to the input string using the primitive-recursive list-concatenation operation. The function that interprets a bit list as a natural number is primitive recursive (\texttt{Turing.codePrimBitsNat}), so applying it to the appended string remains primitive recursive. Finally, predecessor is primitive recursive. Its value on a natural number is subtraction by one, with zero remaining zero; for the encoded appended string this is exactly the defining subtraction in $r(s)$.

**Key facts.** `Turing.codePrimBitsNat`.
