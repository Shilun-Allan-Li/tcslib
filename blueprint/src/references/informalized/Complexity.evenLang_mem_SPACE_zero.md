<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/SpaceComplexity/ZeroSpace.lean :: Complexity.evenLang_mem_SPACE_zero -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Even parity uses zero space

**Claim.** The even-parity language is decidable with zero work-tape space in the stated sense.

**Proof.** Take the even-parity scan machine and set the multiplicative constant to $0$. For every input, the scan machine has a halting computation producing the indicator of even parity in $|x|+1$ steps (`evenScanTM_decidesInTime`). Since this machine has zero work tapes, the zero-tape space theorem converts these computations into a zero-space computation on every input (`computesInSpace_zero_of_k_eq_zero`). This is precisely the witness required for membership in the space class with bound constantly equal to zero.

**Key facts.** `Complexity.evenScanTM_decidesInTime`, `Turing.FinTM.computesInSpace_zero_of_k_eq_zero`.
