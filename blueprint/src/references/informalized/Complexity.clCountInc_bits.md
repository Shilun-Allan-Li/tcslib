<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CookLevin/Hardness.lean :: Complexity.clCountInc_bits -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Binary Increment and Successor

**Claim.** For every natural number $n$, applying the specified list increment to the little-endian binary representation of $n$ gives the little-endian binary representation of $n+1$.

**Proof.** Use binary recursion on $n$. At zero, the representation is empty and incrementing the empty list gives the one-bit representation of $1$. For the recursive case, write the binary representation as the representation of $n$ followed by the final bit $b$, using the decomposition of binary digits for a number formed by appending a bit. If $b$ is false, incrementing changes that final bit to true, giving the representation of the corresponding odd successor (`Nat.bit1_bits`). If $b$ is true, the increment changes it to false and recursively increments the lower bits. By the induction hypothesis those lower bits represent $n+1$; the resulting value is $2(n+1)$, whose representation is obtained by appending a zero bit (`Nat.bit0_bits`). This is the binary representation of the successor in this case as well.
