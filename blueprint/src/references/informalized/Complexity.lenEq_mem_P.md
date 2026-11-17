<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/ClassNP/PClosure.lean :: Complexity.lenEq_mem_P -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Equal decoded lengths are polynomial-time decidable

**Claim.** For a binary string $z$, the language in which the two total decoded components have equal length belongs to $\mathsf{P}$.

**Proof.** The Boolean test that returns true exactly when the two total decoded components of $z$ have equal length is polynomial-time computable (`Complexity.polyTimeComputable_lenEq`). The result that the true set of any polynomial-time computable Boolean test belongs to $\mathsf{P}$ (`Complexity.mem_P_of_test`) therefore applies to this test. Its true set is precisely the language in the claim.

**Key facts.** `Complexity.polyTimeComputable_lenEq`, `Complexity.mem_P_of_test`.
