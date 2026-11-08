<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/Randomized/SpaceAmplifyPoly.lean :: Randomized.PolyAmp.bigK_le -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Amplification Parameter Bound

**Claim.** For all natural numbers $F$ and $n$, the amplification parameter satisfies $2^{F\ell(n)}\le 4^F(n+1)^F$.

**Proof.** First, the binary-length estimate `two_pow_bits_le` gives $2^{|\operatorname{bits}(n)|}\le 2n+1$. Since $\ell(n)=|\operatorname{bits}(n)|+1$, doubling yields $2^{\ell(n)}\le 4n+2\le 4(n+1)$. Raising this inequality to the natural power $F$ preserves its direction. Finally, the definition of the amplification parameter and the power laws give $2^{F\ell(n)}=(2^{\ell(n)})^F\le (4(n+1))^F=4^F(n+1)^F$.

**Key facts.** `Randomized.PolyAmp.two_pow_bits_le`.
