<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter07/TestingAmplification.lean :: FABL.expect_pair_prod_finArrow -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Product expectation on sign cubes

**Claim.** For coordinate functions $g_i$ of two signs, the average over independent uniform sign cubes $x,y$ of $\prod_{i<d}g_i(x_i,y_i)$ equals the product over coordinates of the corresponding two-sign averages.

**Proof.** Fix the first cube $x$. Averaging over the second cube factors the product coordinate by coordinate, by the product expectation formula for functions on a finite function space (`expect_prod_finArrow`). This gives the product over $i$ of the averages over $b$ of $g_i(x_i,b)$. Now average over $x$ and apply the same coordinate factorization again, this time to the functions $a\mapsto \mathbb E_b g_i(a,b)$. The resulting product consists of the iterated averages over $a$ and $b$, as required.

**Key facts.** `FABL.expect_prod_finArrow`.
