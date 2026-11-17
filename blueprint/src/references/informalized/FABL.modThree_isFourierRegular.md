<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter06/Pseudorandomness/ModThree.lean :: FABL.modThree_isFourierRegular -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Fourier regularity bound

**Claim.** Every nonempty subset has Fourier coefficient for the mod-three indicator of absolute value at most $\frac23(\frac{\sqrt3}{2})^n$.

**Proof.** To establish Fourier regularity, take any nonempty subset $S$. The bound on the absolute value of its Fourier coefficient is supplied directly by the coefficient estimate for the mod-three indicator (\texttt{abs_fourierCoeff_modThree_le}). Since this holds for each such $S$, it is exactly the required regularity statement.

**Key facts.** `FABL.abs_fourierCoeff_modThree_le`.
