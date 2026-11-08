<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/SpaceComplexity/Logspace/Mult.lean :: Complexity.mult_columns_correct -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Correctness of multiplication columns

**Claim.** The bit string $c$ represents the product of $a$ and $b$ exactly when the final carry after $|a|+|b|$ columns is zero and each output bit is the parity of the incoming carry plus its column sum.

**Proof.** Put $N=|a|+|b|$. The column-value identity says that the weighted sum of the columns through position $N-1$ is $V(a)V(b)$ (`mult_columns_value`). The carry invariant decomposes that same sum as the weighted sum of the column parities plus $2^N K_N$ (`mult_carry_invariant`). The prefix-bit identity, together with $|c|\le N$, expresses $V(c)$ as the weighted sum of its bits through position $N-1$ (`mult_bits_prefix`).

Suppose first that $V(c)=V(a)V(b)$. Combining these identities yields equality between the weighted parity digits, with the extra term $2^N K_N$, and the weighted bits of $c$. Each parity is less than $2$, and each bit is either zero or one. Uniqueness of binary digits therefore forces $K_N=0$ and equality of the corresponding digits at every position (`mult_digits_unique`).

Conversely, assume the final carry is zero and every output bit agrees with the corresponding parity. The weighted-bit sum for $c$ then equals the weighted parity sum. Applying the carry invariant and the column-value identity, and using the vanishing final carry, shows that this sum is $V(a)V(b)$.

**Key facts.** `Complexity.mult_columns_value`, `Complexity.mult_carry_invariant`, `Complexity.mult_bits_prefix`, `Complexity.mult_digits_unique`.
