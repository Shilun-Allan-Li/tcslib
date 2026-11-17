<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter09/NoiseOperatorExercises.lean :: FABL.noiseRpow_pow_sq -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Powers of the Noise Parameter

**Claim.** For $0\le\rho$ and natural $k$, raising $\rho^{1-\lambda}$ to the $k$th power and then squaring gives $((\rho^k)^2)^{1-\lambda}$.

**Proof.** First move the natural power $k$ into the exponent of the real power, so $(\rho^{1-\lambda})^k=\rho^{(1-\lambda)k}$; this is the natural-power rule for real powers. Commutativity of multiplication makes $(1-\lambda)k=k(1-\lambda)$, and the natural-power rule in the base then identifies this with $(\rho^k)^{1-\lambda}$. Squaring and applying the square-of-a-real-power identity (`rpow_sq_eq_sq_rpow`) gives $((\rho^k)^2)^{1-\lambda}$. Its nonnegativity hypothesis holds because $\rho^k\ge0$.

**Key facts.** `FABL.rpow_sq_eq_sq_rpow`.
