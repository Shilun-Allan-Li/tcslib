<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/BLR/LowDegree.lean :: LowDegreeTest.eps_le_half_of_far -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Farness is at most one half

**Claim.** If $f$ is $\varepsilon$-far from degree at most $d$ for $d\ge1$, then $\varepsilon\le1/2$.

**Proof.** Assume instead that $\varepsilon>1/2$. The Fourier-coefficient bound for a function far from degree (`abs_fourier_coeff_le_of_far_from_degree`) gives, for every set $S$, $|\widehat{(-1)^f}(S)|\le1-2\varepsilon$. At the empty set this forces an absolute value, which is nonnegative, to be at most a negative number. This contradiction proves the claimed bound.

**Key facts.** `LowDegreeTest.abs_fourier_coeff_le_of_far_from_degree`.
