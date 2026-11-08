<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter05/KrawtchoukPolynomials.lean :: FABL.coeff_neg_X_pow -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Coefficients of a Signed Monomial Power

**Claim.** The coefficient of $t^k$ in $(-t)^m$ is $(-1)^m$ when $k=m$, and zero otherwise.

**Proof.** Write $(-X)^m$ as the scalar monomial $(-1)^m X^m$ (\texttt{neg\_X\_pow\_eq}). A scalar multiple of $X^m$ has coefficient equal to that scalar in degree $m$ and zero in all other degrees, giving the two cases.

**Key facts.** `FABL.neg_X_pow_eq`.
