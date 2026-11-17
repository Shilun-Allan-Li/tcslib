<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter02/InfluencesAndDerivatives/BooleanInfluence.lean :: FABL.isBoundaryDimensionEdge_andFunction_iff -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Boundary Edges of AND

**Claim.** The AND function changes value across the edge in coordinate $i$ exactly when the endpoint with coordinate $i$ equal to $1$ is the point whose other coordinates are all $-1$.

**Proof.** The endpoint cannot have every coordinate equal to $-1$, because its $i$th coordinate is $1$. Thus the AND function takes value $1$ there. If flipping coordinate $i$ produces a point with every coordinate equal to $-1$, the flipped endpoint has AND value $-1$, so the edge is a boundary edge. In this case the original endpoint has every other coordinate equal to $-1$, hence it is the specified edge. Conversely, for that specified edge, flipping coordinate $i$ makes every coordinate $-1$, so the function changes value. If the flip does not produce the all-$-1$ point, both endpoints have AND value $1$, and there is no boundary. The endpoint condition also ensures that the all-$-1$ flip occurs precisely for the specified edge.
