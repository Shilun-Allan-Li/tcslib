<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/Randomized/PTMEquiv.lean :: Randomized.BPP_PTM_subset_SigmaP_two_inter_PiP_two -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# BPP Lies in the Second Polynomial Hierarchy Levels

**Claim.** Every language decidable by a bounded-error randomized Turing machine in polynomial time belongs to both the second existential and second universal levels of the polynomial hierarchy, and hence to their intersection.

**Proof.** Translate membership in the polynomial-time randomized class into acceptance by the polynomial-time BPP model (`Randomized.inBPP_of_mem_BPP_PTM`). The Sipser–Gács theorem places every language accepted by that model in both the second existential and second universal levels (`Randomized.sipser_gacs_polyTime`). The two memberships together give membership in their intersection.

**Key facts.** `Randomized.inBPP_of_mem_BPP_PTM`, `Randomized.sipser_gacs_polyTime`.
