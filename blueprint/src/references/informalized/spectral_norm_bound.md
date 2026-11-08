<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/KikuchiLDC/LDC/ThreeXOR.lean :: spectral_norm_bound -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Positivity of the bound expression

**Claim.** For positive natural numbers $k,d,\ell$ and $n\ge 2$, there is a positive constant $C_1$ such that $C_1d\sqrt{k\ell\log n}>0$.

**Proof.** Take $C_1=1$, which is positive. Since $k,d,\ell$ are positive, their real casts are positive; and $n\ge2$ gives $\log n>0$. Thus $k\ell\log n>0$, so its square root is positive. Multiplying these positive factors proves the claimed inequality.

**Caveat.** The formal statement proves only positivity of the displayed expression; it does not assert an expected spectral-norm bound.
