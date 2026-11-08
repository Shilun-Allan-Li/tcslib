<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter09/HypercontractivityExercises.lean :: FABL.degreeTruncation_norm_le_two_of_two_le -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Degree truncation norm bound

**Claim.** For $q\ge2$, the uniform $L^q$ norm of the degree-$k$ truncation is at most $(\sqrt{q-1})^k$ times the uniform $L^2$ norm of $f$.

**Proof.** The degree of the truncation is at most $k$ (`fourierDegree_degreeTruncation_le`). The low-degree norm estimate therefore bounds its uniform $L^q$ norm by $(\sqrt{q-1})^k$ times its own uniform $L^2$ norm (`lowDegree_uniformLpNorm_le`). The truncation does not increase the uniform $L^2$ norm (`uniformLpNorm_two_degreeTruncation_le`). Since the factor $(\sqrt{q-1})^k$ is nonnegative, substituting this latter bound into the former proves the result.

**Key facts.** `FABL.fourierDegree_degreeTruncation_le`, `FABL.lowDegree_uniformLpNorm_le`, `FABL.uniformLpNorm_two_degreeTruncation_le`.
