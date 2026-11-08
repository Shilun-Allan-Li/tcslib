<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter03/LearningTheory/SparseSpectrum.lean :: FABL.dualFourierCoeff_subspaceRestriction_eq_sum_fiber -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Fourier coefficients of a subspace restriction

**Claim.** The Fourier coefficient of the restriction of $f$ to $H$ at $\phi$ is the sum of the Fourier coefficients of $f$ at all functionals on $V$ whose restrictions to $H$ equal $\phi$.

**Proof.** Express the restricted coefficient as the expectation over $H$ of $f(h)$ times the Walsh character indexed by $\phi$. Expand $f(h)$ in its Fourier expansion on $V$, then distribute the product and interchange the finite sum with the expectation. For each functional $\psi$ on $V$, the restriction identity for Walsh characters (\texttt{FABL.dualWalshCharacter_dualRestrict}) identifies its character on $H$ with the character of $\psi|_H$. The resulting expected product of the characters indexed by $\psi|_H$ and $\phi$ is $1$ when $\psi|_H=\phi$ and $0$ otherwise, by character orthogonality (\texttt{FABL.expect_dualWalshCharacter_mul}). Thus each summand contributes exactly the coefficient at $\psi$ when its restriction is $\phi$, and zero otherwise. The coefficient-as-expectation formula used at the start is \texttt{FABL.dualFourierCoeff_eq_expect}; the expansion is \texttt{FABL.dual_fourier_expansion}.

**Key facts.** `FABL.dualFourierCoeff_eq_expect`, `FABL.dual_fourier_expansion`, `FABL.dualWalshCharacter_dualRestrict`, `FABL.expect_dualWalshCharacter_mul`.
