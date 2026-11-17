<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/SpaceComplexity/Logspace/ISCountGenCorrect.lean :: Complexity.bits_succ_le -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Binary Expansion Length Bound

**Claim.** If $m\le 2^e+1$, then the least-significant-first binary expansion of $m+1$ has length at most $e+2$.

**Proof.** The length of the binary expansion of a natural number is its binary size, so it suffices to bound the size of $m+1$. The hypothesis gives $m+1\le 2^e+2$. Also, $2^e+2<2^{e+2}$: expanding $2^{e+2}=4\cdot2^e$, this follows from $1\le2^e$. Thus $m+1<2^{e+2}$, which by the size bound for numbers below a power of two gives binary size at most $e+2$.
