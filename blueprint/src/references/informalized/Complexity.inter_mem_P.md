<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/ClassNP/PClosure.lean :: Complexity.inter_mem_P -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Intersection closure of polynomial time

**Claim.** If two languages over the binary alphabet belong to $\mathsf{P}$, then the language of strings belonging to both also belongs to $\mathsf{P}$.

**Proof.** Use the polynomial-time test supplied for each language (\(\texttt{Complexity.test_of_mem_P}\)). The conjunction of these tests is polynomial-time computable by the closure of polynomial-time tests under conjunction (\(\texttt{Complexity.polyTimeComputable_and}\)). The theorem turning such a test into a language in \(\mathsf{P}\) (\(\texttt{Complexity.mem_P_of_test}\)) therefore puts the language accepted by the conjunction in \(\mathsf{P}\). For each string, the conjunction returns true exactly when both original tests return true, which is exactly membership in the intersection.

**Key facts.** `Complexity.test_of_mem_P`, `Complexity.polyTimeComputable_and`, `Complexity.mem_P_of_test`.
