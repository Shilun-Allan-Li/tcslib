<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter06/F₂Polynomials/Affine.lean :: FABL.functionAlgebraicDegree_affineMap_coordinate_le_one -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Degree of an affine map coordinate

**Claim.** For an affine map $L$ on the Boolean cube, each coordinate function $x\mapsto (L(x))_i$ has algebraic degree at most $1$.

**Proof.** Fix a coordinate $i$. The linear part of $L$, followed by taking coordinate $i$, is a linear functional: additivity follows by taking the $i$th coordinate of the linear part's additivity. Every such linear functional on the Boolean cube is a dot product with some vector $a$ (`FABL.isF₂Linear_iff_exists_dotProduct`). The affine decomposition of $L$ writes $L(x)$ as its linear part at $x$ plus $L(0)$. Consequently its $i$th coordinate is $(L(0))_i+a\cdot x$, so it is an affine Boolean function. The degree bound for affine Boolean functions (`FABL.functionAlgebraicDegree_affineFunction_le_one`) now gives the claim.

**Key facts.** `FABL.isF₂Linear_iff_exists_dotProduct`, `FABL.functionAlgebraicDegree_affineFunction_le_one`.
