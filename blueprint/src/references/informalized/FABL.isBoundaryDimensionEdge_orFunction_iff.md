<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter02/InfluencesAndDerivatives/BooleanInfluence.lean :: FABL.isBoundaryDimensionEdge_orFunction_iff -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Boundary Edges of OR

**Claim.** The OR function changes value across the edge in coordinate $i$ exactly when the endpoint has every coordinate equal to $1$.

**Proof.** After flipping coordinate $i$, the point cannot have every coordinate equal to $1$: its $i$th coordinate is $-1$. Thus the OR value at the flipped endpoint is $-1$. If the original endpoint has every coordinate equal to $1$, its OR value is $1$, so the edge is a boundary. If it does not, its OR value is also $-1$, and the edge is not a boundary. The endpoint condition makes the all-$1$ case precisely the specified edge.
