<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter06/FoolingF₂Polynomials/ViolaAuxiliary.lean :: FABL.sq_le_violaError -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Error Bound by Viola Error

**Claim.** For $0\le\varepsilon\le1$ and $d\ge1$, one has $\varepsilon^2\le 9\varepsilon^{1/2^{d-1}}$.

**Proof.** Set $a=1/2^{d-1}$. Since $d-1\ge0$, the denominator is at least $1$, so $0\le a\le1$, in particular $a\le2$. For a base in $[0,1]$, increasing the exponent can only decrease its real power; hence $\varepsilon^2\le\varepsilon^a$. Also $\varepsilon^a\ge0$, so $\varepsilon^a\le9\varepsilon^a$. The latter expression is exactly the defined Viola error.
