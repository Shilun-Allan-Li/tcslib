<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter06/Constructions/ExecutableFiniteFields.lean :: FABL.buildExecutableBinaryFieldModel_resource_bounds -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Binary Field Model Resource Bounds

**Claim.** For every positive integer $\ell$, the constructed model has $2^\ell$ elements and each operation table has $2^{2\ell}$ entries; its representation bit count is at most its preprocessing work, that work is at most $2^{8(\ell+1)}$, and its arithmetic work is at most $8(\ell+1)^2$.

**Proof.** Unfold the model construction and apply the established list-length formulas: the binary-vector enumeration has length $2^\ell$, and each operation table, indexed by ordered pairs from that enumeration, has length $2^{2\ell}$. The representation-bit count is bounded by the preprocessing work by its defining estimate. The preprocessing-work bound and arithmetic-work bound are then supplied by their respective estimates. Together these six facts give the stated resource bounds.

**Key facts.** `FABL.length_allBinaryVectors`, `FABL.length_binaryAdditionTable`, `FABL.length_binaryMultiplicationTable`, `FABL.binaryFieldRepresentationBits_le_preprocessingWork`, `FABL.binaryFieldPreprocessingWork_le`, `FABL.binaryArithmeticWork_le`.
