<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/BLR/BoolBLR.lean :: BoolBLR.BLR_soundness_via_fourier -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Fourier-Cube Bound from Distance

**Claim.** If the Boolean function is at least $\varepsilon$ far from every linear Boolean function, then the sum of the cubes of the Fourier coefficients of its sign lift is at most $1-2\varepsilon$.

**Proof.** For each subset $S$, the coefficient bound for functions far from linear gives $\widehat F(S)\le 1-2\varepsilon$ (BoolBLR.BLR_soundness_via_fourier_aux_h_bound). Since $\widehat F(S)^2\ge0$, multiplying this inequality by the square yields $\widehat F(S)^3\le \widehat F(S)^2(1-2\varepsilon)$. Sum over all $S$ and factor out the common right-hand factor. Parseval for the sign lift says $\sum_S\widehat F(S)^2=1$ (BoolBLR.BLR_soundness_via_fourier_aux_hparseval), so the resulting upper bound is $1-2\varepsilon$.

**Key facts.** `BoolBLR.BLR_soundness_via_fourier_aux_h_bound`, `BoolBLR.BLR_soundness_via_fourier_aux_hparseval`.
