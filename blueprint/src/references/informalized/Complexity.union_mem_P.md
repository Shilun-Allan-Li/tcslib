<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/ClassNP/PClosure.lean :: Complexity.union_mem_P -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Polynomial Time Is Closed Under Union

**Claim.** If $L_1$ and $L_2$ are polynomial-time decidable languages of finite Boolean words, then their union is also polynomial-time decidable.

**Proof.** By `test_of_mem_P`, each language has a polynomial-time computable Boolean indicator. Compute the indicator of $L_1$ first; if it is true, output the one-bit string `[true]`, and otherwise compute and output the indicator of $L_2`. The conditional-composition fact `polyTimeComputable_ite`, together with the constant-time computability of the fixed output `[true]` (`polyTimeComputable_const`), shows that this procedure is polynomial-time computable. For each input, its Boolean result is true precisely when the input belongs to $L_1$ or, if it does not, belongs to $L_2$; equivalently, it belongs to the union. The characterization of polynomial-time languages by polynomial-time computable tests (`mem_P_of_test`) therefore gives the result.

**Key facts.** `Complexity.test_of_mem_P`, `Complexity.polyTimeComputable_const`, `Complexity.polyTimeComputable_ite`, `Complexity.mem_P_of_test`.
