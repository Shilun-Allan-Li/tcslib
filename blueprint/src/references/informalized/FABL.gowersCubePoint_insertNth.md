<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter06/Gowers.lean :: FABL.gowersCubePoint_insertNth -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Insertion Identity for Gowers Cube Points

**Claim.** Inserting $h$ into the list of directions and $b$ into the corresponding Boolean index produces the same cube point as shifting the base point from $x$ to $x+bh$ and retaining the original directions and index.

**Proof.** Expand the cube point as the base point plus the sum of the coordinatewise scalar multiples. Separate the summand at the insertion position $i$ from all the other summands, which are indexed by the positions strictly before or after $i$. The inserted coordinate contributes $b h$, while the remaining terms are exactly the original sum $\sum_{j<k}s_jy_j$. Regrouping gives $x+bh+\sum_{j<k}s_jy_j$, the cube point based at $x+bh$.
