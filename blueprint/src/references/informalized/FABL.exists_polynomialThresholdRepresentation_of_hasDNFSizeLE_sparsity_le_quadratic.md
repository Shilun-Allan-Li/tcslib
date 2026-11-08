<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter05/DNFSparsePolynomialThreshold.lean :: FABL.exists_polynomialThresholdRepresentation_of_hasDNFSizeLE_sparsity_le_quadratic -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Quadratic Sparsity Bound for DNF Thresholds

**Claim.** A Boolean function computed by a DNF of size at most $s$ has a polynomial threshold representation with sparsity at most $17ns^2$.

**Proof.** The size bound supplies a DNF formula $\varphi$ computing the given function. Apply the quadratic sparsity theorem for DNF formulas to obtain a polynomial threshold representation of $\varphi$ with sparsity at most $17n\,\mathrm{size}(\varphi)^2$ (`DNFFormula.exists_polynomialThresholdRepresentation_sparsity_le_quadratic`). Since $\mathrm{size}(\varphi)\le s$, its square is at most $s^2$; multiplying by $17n\ge0$ gives the claimed bound. The formula computes the original function, so this representation applies to it as well.

**Key facts.** `FABL.DNFFormula.exists_polynomialThresholdRepresentation_sparsity_le_quadratic`.
