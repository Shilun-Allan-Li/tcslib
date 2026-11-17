<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter06/Gowers.lean :: FABL.prod_gowersNorm_monotonicityFamily -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Product of monotonicity-family norms

**Claim.** The product of the order-$(k+1)$ Gowers norms of the monotonicity-family functions over all indices equals the order-$(k+1)$ Gowers norm of $f$ raised to $2^k$.

**Proof.** Split each index of the $(k+1)$-dimensional cube according to its last coordinate. The cube-index product decomposition ( `prod_f₂Cube_succ`) writes the full product as the product over indices ending in $0$ times the product over those ending in $1$. In the first group, the family function is $f$, so there are $2^k$ identical norm factors; in the second, it is the constant-one function, whose Gowers norm is $1$ because $k+1>0$. The cardinality of the $k$-dimensional cube is $2^k$ (`card_f₂Cube`), so the first group contributes the stated power and the second contributes $1$.

**Key facts.** `FABL.prod_f₂Cube_succ`, `FABL.card_f₂Cube`, `FABL.gowersNorm_one`.
