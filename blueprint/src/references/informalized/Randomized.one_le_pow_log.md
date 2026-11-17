<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/Randomized/QuasiPolyHierarchy.lean :: Randomized.one_le_pow_log -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Power of the Binary Logarithm

**Claim.** For every natural number $n$, $1\le n^{\lfloor\log_2 n\rfloor}$, where the exponent is the natural-number logarithm of $n$ to base $2$.

**Proof.** Split into the cases $n=0$ and $n>0$. When $n=0$, the natural logarithm exponent is zero, so the power is $0^0=1$. When $n>0$, every natural power of $n$ is at least $1$, so in particular this holds for exponent $\operatorname{Nat.log}(2,n)$.
