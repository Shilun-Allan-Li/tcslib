<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter06/F₂Polynomials/Affine.lean :: FABL.functionAlgebraicDegree_anfMonomial_comp_affineMap_le_card -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Degree after affine substitution

**Claim.** For an affine map $L$ and a subset $S$ of coordinates, the function $x\mapsto\prod_{i\in S}(L(x))_i$ has algebraic degree at most $|S|$.

**Proof.** View the substituted monomial as the product, over $i\in S$, of the coordinate functions $x\mapsto (L(x))_i$. The degree of a finite product is at most the sum of the degrees of its factors (`FABL.functionAlgebraicDegree_finset_prod_le`). Each factor has degree at most one by the affine-map coordinate bound (`FABL.functionAlgebraicDegree_affineMap_coordinate_le_one`). Summing these bounds over $S$ gives at most $|S|.

**Key facts.** `FABL.functionAlgebraicDegree_finset_prod_le`, `FABL.functionAlgebraicDegree_affineMap_coordinate_le_one`.
