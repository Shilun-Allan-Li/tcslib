<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/ClassP/TimeConstructible.lean :: Complexity.counterInc_bits -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Incrementing a Binary Representation

**Claim.** For every natural number $n$, incrementing its least-significant-bit-first binary representation produces the least-significant-bit-first binary representation of $n+1$.

**Proof.** Use binary recursion on $n$. At zero, the representation is empty and the increment rule produces the one-bit representation $[1]$. For the recursive case, write the number in the form represented by a low bit $b$ followed by the representation of a smaller number $n$. The standard decomposition of binary digits (Nat.bits_append_bit) lets us compute the increment by considering $b$. If $b=0$, incrementing changes that low bit to $1$ and leaves the remaining digits unchanged; this is precisely the binary representation of the odd number $2n+1$ (Nat.bit1_bits). If $b=1$, incrementing changes that bit to $0$ and recursively increments the remaining digits. By the induction hypothesis the remaining digits represent $n+1$, so the resulting word represents $2(n+1)$. The binary representation of this even number is a low zero followed by the representation of $n+1$ (Nat.bit0_bits), as required.
