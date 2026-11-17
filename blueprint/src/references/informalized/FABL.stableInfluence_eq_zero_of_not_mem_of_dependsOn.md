<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter06/Pseudorandomness/JuntaStableInfluence.lean :: FABL.stableInfluence_eq_zero_of_not_mem_of_dependsOn -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Influence Outside the Dependence Set

**Claim.** If $f$ depends only on coordinates in $J$, then for every $i\notin J$ and every real $\rho$, the stable influence of $f$ at $i$ is zero.

**Proof.** In the stable-influence sum, every index set $S$ contains $i$. Since $i\notin J$, such an $S$ cannot be a subset of $J$. A Fourier coefficient vanishes whenever its index set is not contained in a set of coordinates on which the function depends (`fourierCoeff_eq_zero_of_dependsOn_of_not_subset`). Thus every summand has a zero squared Fourier coefficient, and the whole sum is zero.

**Key facts.** `FABL.fourierCoeff_eq_zero_of_dependsOn_of_not_subset`.
