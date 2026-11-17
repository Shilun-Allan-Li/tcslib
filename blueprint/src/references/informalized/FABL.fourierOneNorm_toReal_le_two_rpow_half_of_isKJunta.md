<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter06/Pseudorandomness/RegularityCharacterizations.lean :: FABL.fourierOneNorm_toReal_le_two_rpow_half_of_isKJunta -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Fourier norm of a junta

**Claim.** If a sign-valued function depends only on a set of at most $k$ coordinates, then the Fourier one-norm of its real sign representation is at most $2^{k/2}$.

**Proof.** Choose a coordinate set $J$ of size at most $k$ on which the function depends. This dependence passes to its real sign representation by \texttt{dependsOn_toReal_iff}. Every Fourier coefficient indexed by a set not contained in $J$ vanishes, by \texttt{fourierCoeff_eq_zero_of_dependsOn_of_not_subset}; thus the norm sum is supported on the subsets of $J$. By Parseval’s identity (\texttt{sum_sq_fourierCoeff_eq_one}), the sum of the squared coefficients over these subsets is at most $1$. Cauchy–Schwarz therefore bounds the sum of their absolute values by the square root of the number of subsets of $J$ times the square root of that squared-coefficient sum. There are $2^{|J|}$ such subsets, so the resulting bound is $2^{|J|/2}$. Since $|J|\le k$, monotonicity of $2^t$ gives the claimed bound $2^{k/2}$.

**Key facts.** `FABL.dependsOn_toReal_iff`, `FABL.fourierCoeff_eq_zero_of_dependsOn_of_not_subset`, `FABL.sum_sq_fourierCoeff_eq_one`.
