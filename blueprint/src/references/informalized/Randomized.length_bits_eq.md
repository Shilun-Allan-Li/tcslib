<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/Randomized/QuasiPolyHierarchy.lean :: Randomized.length_bits_eq -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Binary Expansion Length

**Claim.** For every natural number $n$, its binary expansion has length $0$ when $n=0$, and otherwise has length $\lfloor\log_2 n\rfloor+1$.

**Proof.** The length of the binary expansion equals the binary size of $n$. When $n=0$, both are zero. For $n>0$, the strict logarithmic power bound shows that $n<2^{\operatorname{Nat.log}(2,n)+1}$, so the size is at most $\operatorname{Nat.log}(2,n)+1$. Conversely, the power-of-logarithm bound gives $2^{\operatorname{Nat.log}(2,n)}\le n$; therefore the size is at least $\operatorname{Nat.log}(2,n)+1$. These bounds identify the size, and hence the expansion length, with the claimed value.
