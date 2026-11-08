<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/BLR/LowDegree.lean :: LowDegreeTest.fourier_coeff_le_of_far_from_degree -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Fourier coefficients under farness

**Claim.** If $f$ is $\varepsilon$-far from degree at most $d$, then every Fourier coefficient of its $\pm1$ lift is at most $1-2\varepsilon$.

**Proof.** Fix a set $S$ and choose the Boolean function whose $\pm1$ lift is the character $\chi_S$: its value is the parity of the coordinates in $S$ where the input is true. The proof verifies that this parity function has the stated character as its lift. The character has degree at most $d$ (`char_is_degree_le`), so farness gives distance at least $\varepsilon$ between it and $f$. The Fourier-coefficient bound in terms of distance (`fourier_coeff_le_of_dist_ge`) now yields $\widehat{(-1)^f}(S)\le1-2\varepsilon$.

**Key facts.** `BoolBLR.fourier_coeff_le_of_dist_ge`, `LowDegreeTest.char_is_degree_le`.
