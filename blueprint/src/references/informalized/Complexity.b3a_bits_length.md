<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/SpaceComplexity/Constructible.lean :: Complexity.b3a_bits_length -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Length of the binary expansion

**Claim.** For every nonzero natural number $n$, the length of its binary digit list is $\log_2(n)+1$, where $\log_2$ is the integer logarithm used in the definition of logarithmic space.

**Proof.** The general upper bound on binary digit length gives $|n.\mathrm{bits}|\leq \mathrm{Nat.log}\,2\,n+1$ (Complexity.LogProg.length_bits_le_log). For the reverse inequality, the standard size estimate says that $2^{\mathrm{Nat.log}\,2\,n}\leq n$; together with the strict bound that a number is less than the power of two given by its size, this yields $\mathrm{Nat.log}\,2\,n+1\leq \mathrm{Nat.size}\,n$. For nonzero $n$, its size equals the length of its binary digit list. The two inequalities therefore give the claimed equality, since logarithmic space here is defined as $\mathrm{Nat.log}\,2\,n+1$.

**Key facts.** `Complexity.LogProg.length_bits_le_log`.
