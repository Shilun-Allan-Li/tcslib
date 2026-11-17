<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter03/LowDegreeSpectralConcentration.lean :: FABL.booleanInfluence_eq_zero_of_fourierDegree_le_zero -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Zero influence at degree zero

**Claim.** If the Fourier degree of the real-valued version of a Boolean function is at most zero, then every coordinate has zero influence.

**Proof.** Rewrite Boolean influence as the influence of the real-valued function (`booleanInfluence_eq_influence_toReal`), and express that influence as the sum of squared Fourier coefficients over sets containing the chosen coordinate (`influence_eq_sum_sq_fourierCoeff`). Every set in this sum is nonempty, since it contains that coordinate. Degree at most zero forces the Fourier coefficient of every nonempty set to vanish (`fourierDegree_le_iff`). Consequently every summand is zero, and so is the influence.

**Key facts.** `FABL.booleanInfluence_eq_influence_toReal`, `FABL.influence_eq_sum_sq_fourierCoeff`, `FABL.fourierDegree_le_iff`.
