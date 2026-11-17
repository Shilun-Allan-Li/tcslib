<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter03/SubspacesAndDecisionTrees/DecisionTreeFourier.lean :: FABL.F₂DecisionTree.spectralPNorm_one_pathExpansion_le_sum_abs_output -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Spectral Norm of a Path Expansion

**Claim.** For any finite list of real-output paths, the spectral $1$-norm of its path expansion is at most the sum of the absolute values of the path outputs.

**Proof.** Induct on the list. For the empty list, the expansion is zero, so all its Fourier coefficients vanish and its spectral $1$-norm is zero. For a cons, the expansion is the sum of the first path’s output times its indicator and the tail expansion (`pathExpansion_cons`). The spectral $1$-norm satisfies the triangle inequality (`spectralPNorm_one_add_le`), so it is bounded by the sum of the norms of those two terms. The norm of a constant multiple is the absolute value of the constant times the norm (`spectralPNorm_one_const_mul`); moreover, every path indicator has spectral $1$-norm one (`Path.spectralPNorm_one_indicator`). Thus the first term contributes exactly the absolute value of that path’s output. Apply the induction hypothesis to the tail and combine the two bounds. The resulting sum is precisely the sum of absolute outputs over the cons list.

**Key facts.** `FABL.vectorFourierCoeff_eq_expect`, `FABL.F₂DecisionTree.pathExpansion_cons`, `FABL.spectralPNorm_one_add_le`, `FABL.spectralPNorm_one_const_mul`, `FABL.F₂DecisionTree.Path.spectralPNorm_one_indicator`.
