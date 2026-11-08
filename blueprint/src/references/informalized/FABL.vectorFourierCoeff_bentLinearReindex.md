<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter06/Constructions/BentFunctions.lean :: FABL.vectorFourierCoeff_bentLinearReindex -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Fourier Coefficients Under Linear Reindexing

**Claim.** For an invertible linear map $M$ on the binary cube, the vector Fourier coefficient of $f\circ M$ at $\gamma$ equals the vector Fourier coefficient of $f$ at the frequency obtained by transporting $\gamma$ through the dual action of $M$.

**Proof.** Express both coefficients as expectations of the function times its Walsh character (`FABL.vectorFourierCoeff_eq_expect`). Reindex the first expectation by the bijection $x\mapsto Mx$; the function term then becomes $f(x)$. The character term transforms according to the dual-frequency identity: the dot product of the transported frequency with $y$ equals the dot product of $\gamma$ with $M^{-1}y$ (`FABL.f₂DotProduct_bentDualFrequency`). Taking $y=Mx$ makes this dot product the one defining the original character at $x$. Since a Walsh character is the binary sign of that dot product (`FABL.vectorWalshCharacter_apply`), the character terms agree, and hence the expectations agree.

**Key facts.** `FABL.vectorFourierCoeff_eq_expect`, `FABL.vectorWalshCharacter_apply`, `FABL.f₂DotProduct_bentDualFrequency`.
