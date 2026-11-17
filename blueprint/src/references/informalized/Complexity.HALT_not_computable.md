<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/Uncomputability/Halting.lean :: Complexity.HALT_not_computable -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Uncomputability of the Halting Function

**Claim.** For every effective machine representation scheme $c$, no finite-state Boolean Turing machine computes the function that outputs the one-bit list containing the value of $\mathrm{HALT}_c$ on each input.

**Proof.** Suppose, for contradiction, that such a machine computes the halting function. The reduction from computing the halting function to computing the universal computation predicate (Complexity.UC_computable_of_HALT_computable) would then make the universal computation predicate computable. This contradicts the uncomputability of that predicate (Complexity.UC_not_computable). Hence the halting function is not computable.

**Key facts.** `Complexity.UC_computable_of_HALT_computable`, `Complexity.UC_not_computable`.
