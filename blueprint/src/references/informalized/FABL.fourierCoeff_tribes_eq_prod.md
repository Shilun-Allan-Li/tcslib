<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter04/Tribes.lean :: FABL.fourierCoeff_tribes_eq_prod -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Product formula for tribes coefficients

**Claim.** The Fourier coefficient of the real-valued tribes function equals the empty-frequency correction plus the stated product of single-block expectations.

**Proof.** Write the real-valued tribes function as twice the product over blocks of the factors $(1+\operatorname{AND}_w)/2$, minus one (`FABL.tribes_toReal_eq`). Rewriting the product of the denominators yields the factor $2\cdot 2^{-s}$ multiplying the product of the numerators, followed by $-1$. Multiply this expression by the monomial at $T$ and take expectations. Linearity separates the constant multiple and the subtracted monomial; the latter expectation is $1$ for empty $T$ and $0$ otherwise (`FABL.expect_monomial`). For the product term, reindex the cube as a tuple of its $s$ blocks using the block equivalence (`FABL.tribesBlockEquiv_apply`). The monomial factors into the product of the monomials on the frequency parts of each block (`FABL.monomial_eq_prod_tribeFrequencyPart`). The expectation of this product over independent, uniformly ranging blocks factors into the product of the block expectations (`FABL.expect_prod_finArrow`). Combining these identities gives the claimed formula.

**Key facts.** `FABL.tribes_toReal_eq`, `FABL.expect_monomial`, `FABL.tribesBlockEquiv_apply`, `FABL.monomial_eq_prod_tribeFrequencyPart`, `FABL.expect_prod_finArrow`.
