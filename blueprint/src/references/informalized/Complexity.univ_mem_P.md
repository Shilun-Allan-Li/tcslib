<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/ClassNP/PClosure.lean :: Complexity.univ_mem_P -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# The Full Binary Language Is in Polynomial Time

**Claim.** The language of all finite binary strings belongs to the class of polynomial-time decidable languages.

**Proof.** The constant function that outputs `[true]` is polynomial-time computable (`polyTimeComputable_const`). Its Boolean test is true on every input, so the test-characterization theorem `mem_P_of_test` places the language defined by this test in $\mathsf P$. This is exactly the full language of finite Boolean strings.

**Key facts.** `Complexity.polyTimeComputable_const`, `Complexity.mem_P_of_test`.
