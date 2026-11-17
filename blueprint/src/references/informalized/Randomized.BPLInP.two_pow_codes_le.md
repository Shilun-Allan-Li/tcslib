<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/Randomized/BPLInP.lean :: Randomized.BPLInP.two_pow_codes_le -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Exponential bound for machine codes

**Claim.** For every input length $n$, the displayed power of two is bounded above by the stated product involving powers of $8$ and $n+1$.

**Proof.** Put $m=|\mathrm{bits}(n)|$. First, $\mathrm{logSpace}(n)\le m+1$. At $n=0$ this follows directly from the definitions; for positive $n$, the logarithm is strictly less than the binary size, and binary size equals $m$. Next, $2^m\le2(n+1)$. This is immediate at zero. For positive $n$, binary size is positive and its predecessor has power of two at most $n$; multiplying by two gives the claimed bound. Set $e=\mathrm{codeK}(N)(c+1)$. The logarithmic estimate and elementary rearrangement of the exponents show that the exponent on the left is at most $e(m+2)$. Thus the left side is at most $2^{e(m+2)}=(4\cdot2^m)^e$. Using $2^m\le2(n+1)$ bounds this by $(8(n+1))^e$, which factors as $8^e(n+1)^e$, the desired right side.
