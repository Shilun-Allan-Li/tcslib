<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/BLR/LowDegree.lean :: LowDegreeTest.gowers_product_mul -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Multiplicativity of the Gowers product

**Claim.** For any functions $f,g$, order $k$, base point, and directions, the Gowers product of $f\cdot g$ is the product of the Gowers products of $f$ and $g$.

**Proof.** Proceed by induction on $k$, with the base point arbitrary. At order zero, the Gowers product is simply the function value, and the claim is the definition of pointwise multiplication. For the induction step, the recursive definition writes the order-$(k+1)$ product as the product of two order-$k$ products: one based at $x$, and one based at $x\oplus h_{k+1}$, both using the first $k$ directions. Apply the induction hypothesis to each factor. Rearranging the resulting four real factors by commutativity and associativity gives the product of the order-$(k+1)$ products of $f$ and $g$.
