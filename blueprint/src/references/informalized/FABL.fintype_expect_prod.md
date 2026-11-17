<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter07/UniqueGamesReduction.lean :: FABL.fintype_expect_prod -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Iterated Finite Expectation

**Claim.** For finite types $\alpha$ and $\beta$, the uniform average of a function on $\alpha\times\beta$ equals its iterated uniform average, first over $\beta$ and then over $\alpha$.

**Proof.** Regard the product type as the product of the two finite index sets. The uniform expectation over this product is the finite average over the product set, and the finite product-expectation formula rewrites that average as the iterated average over the two factors.
