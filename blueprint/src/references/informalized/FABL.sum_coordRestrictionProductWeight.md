<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter04/Switching.lean :: FABL.sum_coordRestrictionProductWeight -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Total weight of coordinate restrictions

**Claim.** For any finite coordinate set and any real $\delta$, the sum over all assignments of coordinate restrictions of the product of their coordinate weights is $1$.

**Proof.** Sum the product weights over all restriction assignments. The finite product-sum identity factors this sum into a product, one factor for each coordinate, of the sum of the three possible weights at that coordinate. Each such one-coordinate sum is $1$ (`FABL.sum_coordRestrictionWeightAt`). The product is therefore $1.

**Key facts.** `FABL.sum_coordRestrictionWeightAt`.
