<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/Randomized/ZPPHostsClasses.lean :: Randomized.inZPP_subset_ZPPAbort_PTM -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Zero-error algorithms with bounded abort time

**Claim.** Every language with an efficient polynomial-witness zero-error verifier belongs to the class of aborting probabilistic Turing machines with polynomial time bound and correctness probability at least $1/2$.

**Proof.** Apply the inclusion from efficient zero-error verification to expected-polynomial-time zero-error computation (`Randomized.inZPP_subset_ZPP_PTM`), then the inclusion from that class to the bounded-abort machine class (`Randomized.ZPP_PTM_subset_ZPPAbort_PTM`). Transitivity of inclusion gives the claim.

**Key facts.** `Randomized.inZPP_subset_ZPP_PTM`, `Randomized.ZPP_PTM_subset_ZPPAbort_PTM`.
