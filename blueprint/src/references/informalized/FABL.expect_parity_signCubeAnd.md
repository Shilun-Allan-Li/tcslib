<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter07/TestingAmplification.lean :: FABL.expect_parity_signCubeAnd -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Expected parity after conjunction

**Claim.** For a coordinate set $S$, the expected parity of the coordinatewise conjunction $x\wedge y$ on $S$ is $(1/2)^{|S|}.

**Proof.** Expand the parity as the product of the signs of the conjunction at each coordinate in $S$. At each coordinate, the expected sign of the conjunction of two independent uniform signs is $1/2$ (`FABL.expect_signAnd`). The product-expectation lemma factors the expectation across the coordinates in $S$, giving $(1/2)^{|S|}$ (`FABL.expect_subset_pair_product`).

**Key facts.** `FABL.expect_signAnd`, `FABL.expect_subset_pair_product`.
