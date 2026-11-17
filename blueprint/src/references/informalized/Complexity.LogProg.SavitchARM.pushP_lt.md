<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/SpaceComplexity/SavitchARM/Recursion.lean :: Complexity.LogProg.SavitchARM.pushP_lt -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Bound for a Pushed Phase Bit

**Claim.** For natural numbers $w,i,SP$, if $i+1\le w$ and $SP<2^{w-(i+1)}$, then $2SP+1<2^{w-i}$.

**Proof.** Since $i+1\le w$, we have $w-i=(w-(i+1))+1$. Thus the right-hand side is $2\cdot 2^{w-(i+1)}$. The hypothesis gives $2SP<2\cdot 2^{w-(i+1)}$, and the left side $2SP+1$ is still strictly below that even integer. Hence $2SP+1<2^{w-i}$.
