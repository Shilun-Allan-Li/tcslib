<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/Randomized/RPExpected.lean :: Randomized.RP_ExpPTM_eq_RP_PTM -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Equality of Randomized Time Classes

**Claim.** The class defined using polynomial bounds on cumulative nonhalting probabilities and approximate one-sided acceptance is exactly the class decidable in polynomial time with one-sided error and acceptance probability at least $2/3$.

**Proof.** For the inclusion from the expected-time class into the polynomial-time class, take a language in the former. The characterization of that class places it in the abstract one-sided randomized polynomial-time class (Randomized.inRP_of_mem_RP_ExpPTM). The membership characterization of the polynomial-time class identifies that abstract class with the polynomial-time machine definition (Randomized.mem_RP_PTM_iff). For the reverse inclusion, use the established inclusion of polynomial-time one-sided randomized computation in the expected-time class (Randomized.RP_PTM_subset_RP_ExpPTM). The two inclusions give equality.

**Key facts.** `Randomized.inRP_of_mem_RP_ExpPTM`, `Randomized.mem_RP_PTM_iff`, `Randomized.RP_PTM_subset_RP_ExpPTM`.
