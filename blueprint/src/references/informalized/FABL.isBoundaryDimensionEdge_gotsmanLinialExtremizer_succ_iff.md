<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter05/GotsmanLinialExtremizer.lean :: FABL.isBoundaryDimensionEdge_gotsmanLinialExtremizer_succ_iff -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Boundary Edges of the Gotsman–Linial Extremizer

**Claim.** For the Gotsman–Linial extremizer with parameters $m+1$ and $s+1$, the edge in coordinate $i$ is a boundary exactly when the number of positive coordinates after removing $i$ is the starting layer plus some $j$ with $0\le j<s+1$.

**Proof.** Remove coordinate $i$ from the endpoint and write $c$ for the number of positive coordinates in the resulting point, and $a=(m+1-(s+1))/2$ rounded down. The sum of its signs is $2c-m$ ( `sum_signValue_eq_two_mul_positiveCoordinateCount_sub`). The sign sum at the endpoint is one more, and after flipping coordinate $i$ it is one less ( `sum_signValue_dimensionEdge_plus`, `sum_signValue_dimensionEdge_minus`). The extremizer's polynomial on the cube can be written as a product whose factors are determined by these sign sums ( `gotsmanLinialCubePolynomial_eq_product`). Substituting the two sums identifies the two product values with the layer values at $c+1$ and $c$. The threshold signs of consecutive layer values differ exactly when $a\le c<a+(s+1)$ ( `thresholdSign_gotsmanLinialLayerValue_succ_ne_iff`). Finally, this integer interval condition is equivalent to writing $c=a+j$ for an integer $j$ with $0\le j<s+1$: take $j=c-a$ in one direction, and use the stated bounds in the other.

**Key facts.** `FABL.sum_signValue_dimensionEdge_plus`, `FABL.sum_signValue_dimensionEdge_minus`, `FABL.sum_signValue_eq_two_mul_positiveCoordinateCount_sub`, `FABL.gotsmanLinialCubePolynomial_eq_product`, `FABL.thresholdSign_gotsmanLinialLayerValue_succ_ne_iff`.
