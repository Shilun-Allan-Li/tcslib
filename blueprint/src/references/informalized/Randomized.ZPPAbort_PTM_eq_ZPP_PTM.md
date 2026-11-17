<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/Randomized/ZPPHostsClasses.lean :: Randomized.ZPPAbort_PTM_eq_ZPP_PTM -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Equality of zero-error classes

**Claim.** The polynomial-time abort class equals the class decidable in zero-error expected polynomial time.

**Proof.** For the first inclusion, take a language in the abort class. The abort-to-zero-error theorem places it in the abstract zero-error polynomial-time class (`inZPP_of_mem_ZPPAbort_PTM`), and the theorem realizing that class as the machine-based class puts it in `ZPP_PTM` (`inZPP_subset_ZPP_PTM`). The reverse inclusion is exactly the conversion from zero-error expected polynomial time to polynomial time with aborts (`ZPP_PTM_subset_ZPPAbort_PTM`). These two inclusions give equality.

**Key facts.** `Randomized.inZPP_of_mem_ZPPAbort_PTM`, `Randomized.inZPP_subset_ZPP_PTM`, `Randomized.ZPP_PTM_subset_ZPPAbort_PTM`.
