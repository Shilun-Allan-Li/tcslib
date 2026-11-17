<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter06/Pseudorandomness/RegularityComparisons.lean :: FABL.IsLowDegreeFourierRegular.isFourierRegular_and_hasSmallInfluences_of_monotone -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Regularity and Influences for Monotone Functions

**Claim.** If a Boolean function is monotone and its Fourier coefficients of degree at most one satisfy the stated regularity bound, then it is Fourier regular with the same bound and has small influences with that bound.

**Proof.** Fix a coordinate $i$. The degree-one hypothesis applied to the singleton $\{i\}$ bounds the absolute value of its Fourier coefficient by $\varepsilon$. For a monotone Boolean function, this coefficient equals the influence of coordinate $i$ (`influence_eq_fourierCoeff_singleton_of_monotone`), and that influence is nonnegative (`influence_nonneg`). Hence the influence is at most $\varepsilon$. Next, for any nonempty set $S$, choose $i\in S$. Monotonicity gives that the absolute value of the Fourier coefficient indexed by $S$ is at most the influence of $i$ (`abs_fourierCoeff_le_influence_of_monotone`), which is at most $\varepsilon$ by the coordinate bound. This proves Fourier regularity. Finally, the characterization of small influences as the coordinatewise bound on influences (`hasSmallInfluences_iff`) gives the claimed small-influence property.

**Key facts.** `FABL.influence_eq_fourierCoeff_singleton_of_monotone`, `FABL.influence_nonneg`, `FABL.abs_fourierCoeff_le_influence_of_monotone`, `FABL.hasSmallInfluences_iff`.
