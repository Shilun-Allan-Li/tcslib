<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/Randomized/ZPPEquiv.lean :: Randomized.BPP_ExpPTM_eq_BPP_PTM -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Expected-Time and Polynomial-Time BPP

**Claim.** Expected-time and polynomial-time BPP coincide: every language with a randomized decision machine of polynomial expected running time and arbitrarily close to the stated correctness threshold belongs to polynomial-time BPP, and conversely.

**Proof.** Set extensionality reduces equality to proving both inclusions. For the inclusion from expected-time BPP to polynomial-time BPP, the proof identifies membership in BPP with membership in the verifier-based class `InBPP polyTimeModel` (`mem_BPP_PTM_iff`), then uses the theorem that expected-time BPP membership implies membership in that verifier class (`inBPP_of_mem_BPP_ExpPTM`). The opposite inclusion is exactly the previously established containment of polynomial-time BPP in expected-time BPP (`BPP_PTM_subset_BPP_ExpPTM`).

**Key facts.** `Randomized.inBPP_of_mem_BPP_ExpPTM`, `Randomized.mem_BPP_PTM_iff`, `Randomized.BPP_PTM_subset_BPP_ExpPTM`.
