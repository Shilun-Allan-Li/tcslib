<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter06/Gowers.lean :: FABL.expect_prod_type -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Expectation over a product of finite types

**Claim.** For finite types $\alpha$ and $\beta$, the uniform expectation of a real-valued function on $\alpha\times\beta$ equals the iterated uniform expectation, first over $\beta$ and then over $\alpha$.

**Proof.** The full set of pairs is the Cartesian product of the full sets of elements of $\alpha$ and $\beta$. The finite product-expectation formula expresses the uniform average over that Cartesian product as the iterated uniform averages over its two factors. Applying it to the given function gives the stated identity.
