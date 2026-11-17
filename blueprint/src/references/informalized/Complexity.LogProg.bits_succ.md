<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/SpaceComplexity/Machines/Bin.lean :: Complexity.LogProg.bits_succ -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Binary Expansion of a Successor

**Claim.** For every natural number $n$, the bits of $n+1$ are obtained by changing each initial $1$ to $0$ until the first $0$, which is changed to $1$; if there is no such $0$, a $1$ is appended after changing all bits to $0$.

**Proof.** Use strong induction on $n$, so that the result is available for every smaller natural number. At $n=0$, the bit lists of $0$ and $1$ give the stated rule directly. For positive $n$, split by parity. If $n=2m$, positivity gives $m>0$. The bits of $2m$ are obtained by prefixing $0$ to the bits of $m$, while those of $2m+1$ are obtained by prefixing $1$; hence the increment changes that leading $0$ to $1$ and leaves the rest unchanged. If $n=2m+1$, then $n+1=2(m+1)$. The bits-of-$2m+1$ rule gives the bits of $n$ as a leading $1$ followed by the bits of $m$. The induction hypothesis describes the bits of $m+1$; prefixing $0$ to them, using the bits-of-even-number rule, is exactly the stated increment operation on the leading $1$ and the remaining word. The identities for bits of doubled numbers with a trailing bit (`bits_two_mul_add`) provide the needed prefix descriptions in both parity cases.

**Key facts.** `Complexity.LogProg.bits_two_mul_add`.
