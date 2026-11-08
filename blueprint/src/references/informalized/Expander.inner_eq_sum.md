<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/Expanders/Basic.lean :: Expander.inner_eq_sum -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Euclidean Inner Product Formula

**Claim.** For vectors $x,y\in\mathbb{R}^n$, their Euclidean inner product is $\langle x,y\rangle=\sum_{i=1}^n x_i y_i$.

**Proof.** In the coordinate representation of Euclidean space, the inner product is the sum of the products of corresponding coordinates, with complex conjugation on the first coordinate in the general inner product formula. Over the reals conjugation is the identity, so the summand is $x_i y_i$; commutativity of real multiplication gives the stated order.
