<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CookLevin/Hardness.lean :: Complexity.clNum_head -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Value from the First Bit and Tail

**Claim.** For every finite bit string $w$, its little-endian value is twice the value of its tail plus the numeric value of its first bit, with the first bit taken to be $0$ when $w$ is empty.

**Proof.** If $w$ is empty, its tail is empty, its default first bit is false, and both sides are zero. Otherwise write $w=b::v$. Its tail is $v$ and its first bit is $b$. The fold defining the little-endian value applies the natural-number bit operation for $b$ to the value of $v$. That operation equals twice the value of $v$ plus $1$ when $b$ is true, and twice the value of $v$ when $b$ is false. This is precisely the claimed formula using the numeric value of $b$.
