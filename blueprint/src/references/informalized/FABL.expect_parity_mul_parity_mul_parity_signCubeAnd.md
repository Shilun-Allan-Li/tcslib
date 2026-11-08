<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter07/TestingAmplification.lean :: FABL.expect_parity_mul_parity_mul_parity_signCubeAnd -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Three parity factors under conjunction

**Claim.** For a coordinate set $S$, the expected product of the parity values of $x$, $y$, and their coordinatewise conjunction is $(-1/2)^{|S|}.

**Proof.** Write each parity value as the product of its coordinate signs, using the parity-to-monomial identity (`FABL.parityFunction_toReal`). Regroup the three factors coordinate by coordinate. At each coordinate $i\in S$, the resulting factor is $g(x_i,y_i)$, where $g(a,b)$ is the product of the sign values of $a$, $b$, and their conjunction. The one-coordinate expectation of this factor is $-1/2$ (`FABL.expect_signValue_mul_signValue_mul_signAnd`). The product-expectation lemma for a subset of independent uniform coordinate pairs then gives the expectation as the product of $|S|$ identical factors, namely $(-1/2)^{|S|}$ (`FABL.expect_subset_pair_product`).

**Key facts.** `FABL.parityFunction_toReal`, `FABL.expect_signValue_mul_signValue_mul_signAnd`, `FABL.expect_subset_pair_product`.
