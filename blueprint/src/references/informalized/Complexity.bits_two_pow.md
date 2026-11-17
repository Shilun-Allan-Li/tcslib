<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TimeHierarchy/Separation.lean :: Complexity.bits_two_pow -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Binary Digits of a Power of Two

**Claim.** For every natural number $n$, the least-significant-first binary digit list of $2^n$ consists of $n$ zeros followed by a single $1$.

**Proof.** Induct on $n$. At $n=0$, the number is $1$, whose binary digit list is the single bit $1$. For the successor step, write $2^{n+1}$ as the binary-bit operation with bit $0$ applied to $2^n$. Since $2^n$ is positive, the rule for the binary digits of a number with an adjoined bit applies. It prepends a zero to the digit list for $2^n$. By induction that list is $n$ zeros followed by $1$, so the result is $n+1$ zeros followed by $1$.
