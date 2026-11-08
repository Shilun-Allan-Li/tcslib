<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/SpaceComplexity/Machines/Bin.lean :: Complexity.LogProg.length_bits_le_log -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Logarithmic Bound for Binary Expansion

**Claim.** For every natural number $n$, the length of its binary expansion is at most $\operatorname{Nat.log}(2,n)+1$.

**Proof.** The strict inequality $n<2^{\operatorname{Nat.log}(2,n)+1}$ follows from the natural logarithm power bound (`Nat.lt_pow_succ_log_self`), using that $2>1$. Apply the binary-expansion length bound (`Complexity.LogProg.length_bits_le`) with exponent $\operatorname{Nat.log}(2,n)+1$ to obtain the claimed inequality.

**Key facts.** `Complexity.LogProg.length_bits_le`.
