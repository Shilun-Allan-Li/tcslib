<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter04/Parity.lean :: FABL.parityAgreement_forces_concentration_cutoff -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Parity agreement forces a degree cutoff

**Claim.** If a Boolean function agrees with the parity on all coordinates with probability at least $\tfrac12+\varepsilon_0$, and its Fourier weight above degree $k$ is at most $\varepsilon<4\varepsilon_0^2$, then $n\le k$.

**Proof.** Suppose instead that $k<n$. The full coordinate set then has size greater than $k$, so its squared Fourier coefficient is one of the nonnegative terms in the Fourier weight above degree $k$. The full-set coefficient identity (\(\texttt{fourierCoeff\_univ\_eq\_two\_mul\_parityAgreement\_sub\_one}\)) expresses this coefficient as twice the agreement probability minus one, hence it is at least $2\varepsilon_0$. Its square is therefore at least $4\varepsilon_0^2$. But concentration bounds the entire tail, and thus this individual term, by $\varepsilon<4\varepsilon_0^2$, a contradiction. Therefore $n\le k$.

**Key facts.** `FABL.fourierCoeff_univ_eq_two_mul_parityAgreement_sub_one`.
