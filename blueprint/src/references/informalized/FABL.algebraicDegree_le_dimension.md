<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter06/F₂Polynomials/ANF.lean :: FABL.algebraicDegree_le_dimension -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Algebraic degree bounded by dimension

**Claim.** For a coefficient function on subsets of an $n$-dimensional Boolean cube, its algebraic degree is at most $n$.

**Proof.** The degree is the supremum of the cardinalities of subsets in the support. Every such subset is contained in the $n$-element set of coordinates, so its cardinality is at most $n$. Taking the supremum preserves this upper bound.
