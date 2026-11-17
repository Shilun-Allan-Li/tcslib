<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/SpaceComplexity/SavitchARM/Recursion.lean :: Complexity.LogProg.SavitchARM.size_facts -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Exponential Size Bounds

**Claim.** For every natural number $w$, one has $w<2^w$ and $2^w\le 2^{w^2}$.

**Proof.** The first inequality is the standard fact that every natural number is strictly less than its corresponding power of two. For the second, $w\le w^2$ for natural $w$, since $w\le w\cdot w$; monotonicity of exponentiation with base $2$ gives $2^w\le 2^{w^2}$.
