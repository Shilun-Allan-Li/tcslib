<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter05/DNFSparsePolynomialThreshold.lean :: FABL.exists_polynomialThresholdRepresentation_of_hasDNFSizeLE_sparsity_le_cubic -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Cubic Sparsity Bound for DNF Thresholds

**Claim.** A Boolean function computed by a DNF of size at most $s$ has a polynomial threshold representation with sparsity at most $17ns^3$.

**Proof.** Use the quadratic sparsity result to obtain a polynomial threshold representation of the function with sparsity at most $17ns^2$ (`exists_polynomialThresholdRepresentation_of_hasDNFSizeLE_sparsity_le_quadratic`). If $s=0$, the desired cubic bound follows directly from the quadratic bound. Otherwise $s\ge1$, so $s^2\le s^3$. Multiplying by the nonnegative factor $17n$ shows that the same representation has sparsity at most $17ns^3$.

**Key facts.** `FABL.exists_polynomialThresholdRepresentation_of_hasDNFSizeLE_sparsity_le_quadratic`.
