<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/SpaceComplexity/Machines/FragDec.lean :: Complexity.LogProg.bits_head_odd -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# The First Bit and Parity

**Claim.** For every natural number $n$, the head of its binary bit list is absent when $n=0$, and otherwise is the Boolean truth value of the assertion that $n$ is odd.

**Proof.** If $n=0$, its bit list is empty, so its head is absent. Now suppose $n>0$. The parity decomposition of a natural number gives either $n=2q$ or $n=2q+1$; in either case, $n=2q+b$ where $b$ is the Boolean value of the assertion that $n$ is odd. If $q=0$, positivity forces $b$ to be true. Thus the bits-of-$2q+b$ identity (`bits_two_mul_add`) applies and says that the first bit is $b$. Since $n>0$, the conditional expression in the claim selects this head, as required.

**Key facts.** `Complexity.LogProg.bits_two_mul_add`.
