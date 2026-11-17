<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/Randomized/QuasiPolyHierarchy.lean :: Randomized.budgetSeed_eq -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Explicit Budget Seed

**Claim.** For every Boolean word $x$, the specified seed formed from the binary digits of its length equals the stated concatenation of true-bit blocks and a false bit, with block lengths determined by the binary logarithm of $|x|$.

**Proof.** The number of binary digits of a natural number $n$ is $0$ when $n=0$ and otherwise is $\lfloor\log_2 n\rfloor+1$ (`length_bits_eq`). Also, applying the all-true transducer to a list produces a block of true bits whose length is the input length (`allTrue_eq`). Apply these facts to the portions of the binary expansion obtained by dropping its first two digits and its first digit. If $|x|=0$, the zero case of the digit-length formula reduces both sides to the same empty blocks and the intervening false bit. Otherwise, subtracting the dropped digits from the digit count gives block lengths $\lfloor\log_2 |x|\rfloor-1$ and $\lfloor\log_2 |x|\rfloor$, respectively, yielding the claimed concatenation.

**Key facts.** `Randomized.length_bits_eq`, `Randomized.allTrue_eq`.
