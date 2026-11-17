<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter04/DNFFourier.lean :: FABL.expectRandomRestriction_const_mul -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Homogeneity of random restriction expectation

**Claim.** The random restriction expectation of $c$ times a function $g$ equals $c$ times the random restriction expectation of $g$.

**Proof.** Expand the expectation as a finite sum over free-coordinate sets. For each such set, finite expectation is homogeneous, so the expectation of $c\,g$ over its complementary signs is $c$ times the expectation of $g$. Pull this common factor $c$ out of the finite sum, distributing the subset weights and regrouping the products. The remaining sum is precisely the random restriction expectation of $g$.
