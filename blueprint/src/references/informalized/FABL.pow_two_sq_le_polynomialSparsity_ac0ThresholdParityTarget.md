<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter05/AC0ThresholdParitySeparation.lean :: FABL.pow_two_sq_le_polynomialSparsity_ac0ThresholdParityTarget -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Constructed target sparsity bound

**Claim.** For $m\geq 7$, any polynomial threshold representation of the constructed target Boolean function has at least $2^{m^2}$ nonzero Fourier coefficients.

**Proof.** Restrict the representing polynomial to the active coordinates, fixing all inactive coordinates to the assignment used in the target construction and reindexing the active coordinates. The target itself restricts to the mod-two inner product function on two blocks of length $m^2$ (\texttt{ac0ThresholdParityTarget\_activeRestriction}), so the restricted polynomial still represents that inner product function. The inner product sparsity theorem gives at least $2^{m^2}$ nonzero Fourier coefficients for this restricted polynomial (\texttt{pow\_two\_le\_polynomialSparsity\_innerProductModTwo\_of\_pos}). Finally, restricting and reindexing cannot increase Fourier sparsity (\texttt{polynomialSparsity\_reindexedRestriction\_le}), so the original polynomial has at least as many. Since $(m^2)$ is the exponent here, the resulting bound is $2^{m^2}$.

**Key facts.** `FABL.ac0ThresholdParityTarget_activeRestriction`, `FABL.pow_two_le_polynomialSparsity_innerProductModTwo_of_pos`, `FABL.polynomialSparsity_reindexedRestriction_le`.
