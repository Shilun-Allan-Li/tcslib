<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter09/OneBitHypercontractivity.lean :: FABL.oneBit_twoFour -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# One-bit $(2,4)$ hypercontractivity

**Claim.** If $\rho^2\le1/3$, then the $4$-norm of $a+\rho bx$ on a uniform sign is at most the $2$-norm of $a+bx$.

**Proof.** Raise both nonnegative norms to the fourth power. The fourth-power norm identity and the fourth-moment formula for an affine function of a uniform sign (\texttt{uniformLpNorm\_four\_pow\_eq\_expect\_fourth} and \texttt{expect\_affineSign\_fourth}) reduce the left side to $a^4+6a^2(\rho b)^2+(\rho b)^4$. The right side, using the affine-sign $2$-norm formula (\texttt{uniformLpNorm\_two\_affineSign}), becomes $(a^2+b^2)^2$. The hypothesis gives $6\rho^2\le2$, so the mixed term on the left is at most $2a^2b^2$. Also $\rho^4\le1$, so $(\rho b)^4\le b^4$. Adding these bounds gives $a^4+2a^2b^2+b^4=(a^2+b^2)^2$. Taking fourth roots yields the norm inequality.

**Key facts.** `FABL.uniformLpNorm_nonneg`, `FABL.uniformLpNorm_four_pow_eq_expect_fourth`, `FABL.expect_affineSign_fourth`, `FABL.uniformLpNorm_two_affineSign`.
