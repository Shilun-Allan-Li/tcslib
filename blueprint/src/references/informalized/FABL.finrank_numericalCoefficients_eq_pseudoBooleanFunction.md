<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter06/F₂Polynomials/NumericalNormalForm.lean :: FABL.finrank_numericalCoefficients_eq_pseudoBooleanFunction -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Equal dimensions of coefficient and function spaces

**Claim.** The real vector spaces of numerical coefficients on subsets of $\{0,\ldots,n-1\}$ and real-valued functions on the Boolean cube have equal dimension.

**Proof.** For a real-valued function space on a finite domain, its dimension is the cardinality of that domain. Apply this to each space: their dimensions are respectively the number of subsets of $\{0,\ldots,n-1\}$ and the number of Boolean-cube points. The correspondence between subsets and Boolean-cube points is a bijection, so these cardinalities, and therefore the dimensions, agree.
