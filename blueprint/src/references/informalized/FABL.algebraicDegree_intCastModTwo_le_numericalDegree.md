<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter06/F₂Polynomials/FourierToF₂Polynomial.lean :: FABL.algebraicDegree_intCastModTwo_le_numericalDegree -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Algebraic degree under reduction modulo two

**Claim.** For integer-valued coefficients, the algebraic degree after reducing coefficients modulo two is at most the numerical degree before reduction.

**Proof.** By the support characterization for algebraic degree ($\texttt{algebraicDegree_le_iff}$), consider any subset whose integer coefficient is nonzero modulo two. Its integer coefficient cannot be zero, since zero remains zero after reduction. Thus the corresponding real coefficient is nonzero. The numerical degree characterization ($\texttt{numericalDegree_le_iff}$) bounds the subset's cardinality by the original numerical degree, which proves the result.

**Key facts.** `FABL.algebraicDegree_le_iff`, `FABL.numericalDegree_le_iff`.
