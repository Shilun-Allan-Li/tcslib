<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter08/RecursiveNANDComposition.lean :: FABL.expect_pair_mul_separate -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Product expectation factorization

**Claim.** For finite sets $A,B$ and real-valued functions $f$ on $A$ and $g$ on $B$, the uniform average of $f(a)g(b)$ over $A\times B$ is the product of their separate uniform averages.

**Proof.** The universal set of pairs is the Cartesian product of the universal sets of $A$ and $B$. The uniform average over a product set factors into the product of the two uniform averages (`Finset.expect_product` and `Finset.expect_mul_expect`), which gives the formula.
