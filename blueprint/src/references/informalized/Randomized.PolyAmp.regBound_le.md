<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/Randomized/SpaceAmplifyPoly.lean :: Randomized.PolyAmp.regBound_le -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Polynomial Register Bound

**Claim.** For all natural numbers $cS,F,n$, the quantity $n+\ell(n)+(cS+F)\ell(n)+2K_*+2$, where $K_*=2^{F\ell(n)}$, is at most $(cS+F+6+2\cdot4^F)(n+1)^{F+1}$.

**Proof.** Use the estimates $K_*\le 4^F(n+1)^F$ and $\ell(n)\le n+1$. Since $n+1\ge1$, we also have $n+1\le(n+1)^{F+1}$ and $(n+1)^F\le(n+1)^{F+1}$. Thus the terms involving $n$ and $\ell(n)$ are bounded by constant multiples of $(n+1)^{F+1}$, with coefficients respectively $1$ and $cS+F$. The term $2K_*$ is at most $2\cdot4^F(n+1)^{F+1}$. The remaining constant contribution is at most $4(n+1)^{F+1}$; together with the preceding $n$ and $\ell(n)$ contributions, this is covered by the coefficient $6$. Adding these bounds gives the stated coefficient $cS+F+6+2\cdot4^F$.

**Key facts.** `Randomized.PolyAmp.bigK_le`, `Randomized.PolyAmp.ell_le`.
