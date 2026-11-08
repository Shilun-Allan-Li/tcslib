<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/Randomized/SpaceAmplifyPoly.lean :: Randomized.PolyAmp.two_mul_pow_le -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Exponential Bound from a Size Condition

**Claim.** For nonnegative integers $K,n,d$, if $32(n+1)^d\le K$, then $2(8/9)^{\lfloor(K+1)/2\rfloor}\le(1/2)^{(n+1)^d}$.

**Proof.** Put $a=(n+1)^d$, so $a\ge1$. The size hypothesis implies $6(a+1)\le\lfloor(K+1)/2\rfloor$. Since $0<8/9<1$, increasing the exponent can only decrease its power; therefore $(8/9)^{\lfloor(K+1)/2\rfloor}\le((8/9)^6)^{a+1}$. Direct arithmetic gives $(8/9)^6\le1/2$, so the right-hand side is at most $(1/2)^{a+1}$. Multiplying by $2$ yields $(1/2)^a$, as required.
