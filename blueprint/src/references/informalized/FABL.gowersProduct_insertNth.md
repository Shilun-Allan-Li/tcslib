<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter06/Gowers.lean :: FABL.gowersProduct_insertNth -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Factorization across an inserted coordinate

**Claim.** The product over the $(k+1)$-dimensional cube factors as the product of its two slices, according to whether the inserted coordinate is $0$ or $1$.

**Proof.** Reindex the product over the $(k+1)$-cube by pairs $(b,s)$, where $b\in\mathbb F_2$ is the inserted coordinate and $s$ ranges over the remaining $k$ coordinates. The cube-point identity for inserting a direction says that the point associated to $(b,s)$ is $x+b h+\sum_j s_j y_j$. Thus the product becomes an iterated product over $b$ and $s$. Splitting the outer product over the two elements of $\mathbb F_2$ yields the slice with base point $x$ and the slice with base point $x+h$, exactly the two half-cube products in the claim.

**Key facts.** `FABL.gowersCubePoint_insertNth`.
