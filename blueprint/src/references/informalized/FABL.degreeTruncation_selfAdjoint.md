<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter09/HypercontractivityExercises.lean :: FABL.degreeTruncation_selfAdjoint -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Self-adjointness of degree truncation

**Claim.** The uniform inner product of the degree-$k$ truncation of $f$ with $g$ equals the uniform inner product of $f$ with the degree-$k$ truncation of $g$.

**Proof.** Apply Plancherel to both inner products (`plancherel`), writing each as a sum over Fourier sets of products of coefficients. The coefficient of a degree-$k$ truncation at a set $S$ is the original coefficient when $|S|\le k$ and zero otherwise (`fourierCoeff_degreeTruncation`). Thus both sums retain exactly the terms with $|S|\le k$, and those terms agree because multiplication of real coefficients is commutative. The two inner products are equal.

**Key facts.** `FABL.plancherel`, `FABL.fourierCoeff_degreeTruncation`.
