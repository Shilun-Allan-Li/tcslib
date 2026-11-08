<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter07/TestingAmplification.lean :: FABL.expect_parity_mul_parity_signCubeAnd_second -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Second parity correlation under conjunction

**Claim.** For a coordinate set $S$, the expected product of the parity of $y$ on $S$ and the parity of the coordinatewise conjunction $x\wedge y$ on $S$ is $(1/2)^{|S|}.

**Proof.** Rewrite both parity values as products of their coordinate sign values (`FABL.parityFunction_toReal`) and regroup the factors by coordinate. For each coordinate, the resulting function of the two input signs is $g(a,b)=\operatorname{signValue}(b)\operatorname{signValue}(a\wedge b)$, whose one-coordinate expectation is $1/2$ (`FABL.expect_signValue_second_mul_signAnd`). The product-expectation lemma over the coordinates in $S$ therefore gives $(1/2)^{|S|}$ (`FABL.expect_subset_pair_product`).

**Key facts.** `FABL.parityFunction_toReal`, `FABL.expect_signValue_second_mul_signAnd`, `FABL.expect_subset_pair_product`.
