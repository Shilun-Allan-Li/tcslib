<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/Randomized/ZPPHostsClasses.lean :: Randomized.ZPP_PTM_subset_ZPPAbort_PTM -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Zero-error time admits aborts

**Claim.** Every language decidable in zero-error expected polynomial time belongs to the polynomial-time abort class.

**Proof.** Take a language in `ZPP_PTM`. Membership in this union supplies an exponent and a machine that decides the language in zero-error time bounded by a constant multiple of $n^e+1$. The conversion theorem for such a machine produces new natural-number constants and a machine deciding the same language with aborts within a polynomial time bound (`Turing.FinNDTM.ZDecidesInTime.exists_abortDecidesInTime`). That witness places the language in the union defining `ZPPAbort_PTM`.

**Key facts.** `Turing.FinNDTM.ZDecidesInTime.exists_abortDecidesInTime`.
