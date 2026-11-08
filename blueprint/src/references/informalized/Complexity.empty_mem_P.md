<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/ClassNP/PClosure.lean :: Complexity.empty_mem_P -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Polynomial Time for the Empty Language

**Claim.** The empty language over the binary alphabet belongs to $\mathsf{P}$.

**Proof.** The constant Boolean test that always outputs false is polynomial-time computable (`Complexity.polyTimeComputable_const`). The theorem converting any polynomial-time computable Boolean test into a language in $\mathsf P$ (`Complexity.mem_P_of_test`) therefore applies to this test. Its accepted language is precisely $\{z\mid\mathrm{false} = \mathrm{true}\}$, which has no elements.

**Key facts.** `Complexity.polyTimeComputable_const`, `Complexity.mem_P_of_test`.
