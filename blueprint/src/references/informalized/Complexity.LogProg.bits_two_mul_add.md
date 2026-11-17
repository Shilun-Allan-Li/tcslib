<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/SpaceComplexity/Machines/Bin.lean :: Complexity.LogProg.bits_two_mul_add -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Bits of a Doubled Number Plus a Bit

**Claim.** For every natural number $n$ and bit $b$, if $n=0$ implies $b=1$, then the bits of $2n+b$ are formed by placing $b$ before the bits of $n$.

**Proof.** Split on $b$. If $b=0$, the hypothesis forces $n\ne0$, and the standard bits formula for a positive doubled number says that its expansion is prefixed by $0$. If $b=1$, the number is $2n+1$, whose standard bit formula gives a leading $1$ followed by the bits of $n`; this also covers $n=0$.
