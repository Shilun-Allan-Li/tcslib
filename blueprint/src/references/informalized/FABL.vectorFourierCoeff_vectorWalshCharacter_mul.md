<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter06/Constructions/BentFunctions.lean :: FABL.vectorFourierCoeff_vectorWalshCharacter_mul -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Fourier Coefficient Under Character Multiplication

**Claim.** Multiplying $f$ pointwise by the Walsh character indexed by $a$ shifts its Fourier coefficient at $\gamma$ to the coefficient of $f$ at $a+\gamma$.

**Proof.** Write both coefficients as averages using the expectation formula (`FABL.vectorFourierCoeff_eq_expect`). At each point, the integrand on the left contains the factors $\chi_a(x)$, $f(x)$, and $\chi_\gamma(x)$. The product law for Walsh characters (`FABL.vectorWalshCharacter_mul`) combines the two character factors into $\chi_{a+\gamma}(x)$. Commutativity of real multiplication then gives exactly the integrand defining the coefficient of $f$ at $a+\gamma$, so the averages agree.

**Key facts.** `FABL.vectorFourierCoeff_eq_expect`, `FABL.vectorWalshCharacter_mul`.
