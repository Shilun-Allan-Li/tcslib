<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter06/F₂Polynomials/SpectralDegree.lean :: FABL.exists_top_anfCoeff -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# A Nonzero Coefficient at Maximum Degree

**Claim.** Every nonzero Boolean function over $\mathbb F_2$ has an ANF coefficient that is nonzero and whose indexing set has cardinality equal to the function's algebraic degree.

**Proof.** First, some ANF coefficient must be nonzero. If every coefficient vanished, the identity that evaluating the ANF coefficients recovers the function would make the function identically zero, contrary to the hypothesis. Thus the support of the coefficient function is nonempty. This support is finite, so the cardinality function attains its supremum on it. Choose a support set $S$ attaining that maximum. By definition of support its coefficient is nonzero, and its cardinality is exactly the supremum defining the algebraic degree.

**Key facts.** `FABL.anfEval_anfCoeff`, `FABL.mem_anfSupport`.
