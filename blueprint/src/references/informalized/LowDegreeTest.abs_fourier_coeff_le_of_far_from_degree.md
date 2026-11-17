<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/BLR/LowDegree.lean :: LowDegreeTest.abs_fourier_coeff_le_of_far_from_degree -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Fourier coefficient bound from distance

**Claim.** If a Boolean function is \varepsilon-far from every Boolean function of degree at most $d$, then every Fourier coefficient of its $\{-1,1\}1$ lift has absolute value at most $1-2\varepsilon$.

**Proof.** Fix a subset $S$. The upper bound on the coefficient is supplied by the fact that distance from degree at most $d$ forces each Fourier coefficient to be at most $1-2\varepsilon$ (`fourier_coeff_le_of_far_from_degree`). The corresponding fact for the negative coefficient (`neg_fourier_coeff_le_of_far_from_degree`) gives $-\widehat{(-1)^f}(S)\le 1-2\varepsilon$. Together these are precisely the two inequalities equivalent to $|\widehat{(-1)^f}(S)|\le 1-2\varepsilon$.

**Key facts.** `LowDegreeTest.neg_fourier_coeff_le_of_far_from_degree`, `LowDegreeTest.fourier_coeff_le_of_far_from_degree`.
