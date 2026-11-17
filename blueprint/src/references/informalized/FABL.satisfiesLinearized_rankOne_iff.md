<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter07/QuadraticPCPP.lean :: FABL.satisfiesLinearized_rankOne_iff -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Rank-One Linearization Equivalence

**Claim.** The flattening of the rank-one matrix formed from $w$ satisfies the linearized system exactly when $w$ satisfies every equation in the original quadratic system.

**Proof.** Fix an equation in the list. Its linearized equation evaluates the dot product of the flattened coefficient matrix with the flattened rank-one matrix formed from $w$. The dot-product/flattening identity identifies this value with the pairing of the coefficient matrix and that rank-one matrix (`FABL.f₂DotProduct_flattenBinaryMatrix`). By definition, equality of this pairing with the equation’s right-hand side is exactly satisfaction of the original equation by $w$. Applying this equivalence to each equation proves both directions.

**Key facts.** `FABL.f₂DotProduct_flattenBinaryMatrix`.
