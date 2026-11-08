<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter06/F₂Polynomials/Examples.lean :: FABL.innerProductModTwoBit_joinF₂CubeBlocks_eq_sum -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Binary inner product of joined blocks

**Claim.** For vectors $x,y\in\mathbb F_2^n$, the inner product modulo two of their concatenation is $\sum_{i=1}^n x_i y_i$ in $\mathbb F_2$.

**Proof.** The inner product of the joined blocks equals their dot product (`innerProductModTwoBit_joinF₂CubeBlocks`). By the definition of dot product on these finite coordinate vectors, that is the sum of the coordinatewise products, giving the stated formula.

**Key facts.** `FABL.innerProductModTwoBit_joinF₂CubeBlocks`.
