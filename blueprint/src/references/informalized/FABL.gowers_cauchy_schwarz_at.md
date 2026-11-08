<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter06/Gowers.lean :: FABL.gowers_cauchy_schwarz_at -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Coordinatewise Gowers Cauchy–Schwarz inequality

**Claim.** For a family $F$ and a fixed coordinate $i$, its Gowers inner product is at most the product of the square roots of the inner products of the two families obtained by fixing that coordinate to $0$ and to $1$.

**Proof.** The zero-dimensional case has no coordinate $i$, so there is nothing to prove. For positive dimension, split the inner product along coordinate $i$: it is the expectation over the remaining directions of the product of the two half-cube expectations, one for each fixed coordinate value. Call these expectations $A(y)$ and $B(y)$. Cauchy–Schwarz for finite expectations gives $(\mathbb E_y A(y)B(y))^2\le(\mathbb E_y A(y)^2)(\mathbb E_y B(y)^2)$. Since the right-hand factors are nonnegative, taking square roots bounds the absolute value of the product expectation by the product of the square roots. The expectation itself is no greater than its absolute value. Finally, the duplication identity identifies each second moment with the inner product of the corresponding coordinate-fixed family, giving the claim.

**Key facts.** `FABL.gowersInner_split_at`, `FABL.gowersInner_duplicateAt`.
