<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter07/TestingAmplification.lean :: FABL.expect_parity_mul_parity_signCubeAnd_first -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# First parity correlation under conjunction

**Claim.** For a coordinate set $S$, the expected product of the parity of $x$ on $S$ and the parity of the coordinatewise conjunction $x\wedge y$ on $S$ is $(1/2)^{|S|}.

**Proof.** Express each parity as a product of coordinate sign values using the parity-to-monomial identity (`FABL.parityFunction_toReal`), then combine the factors coordinatewise. The contribution at a coordinate is $g(a,b)=\operatorname{signValue}(a)\operatorname{signValue}(a\wedge b)$. Its one-coordinate expectation is $1/2$ (`FABL.expect_signValue_mul_signAnd`). Applying the product-expectation lemma over $S$ yields $(1/2)^{|S|}$ (`FABL.expect_subset_pair_product`).

**Key facts.** `FABL.parityFunction_toReal`, `FABL.expect_signValue_mul_signAnd`, `FABL.expect_subset_pair_product`.
