<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CookLevin/Hardness.lean :: Complexity.clCmp_width -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Bound on Each Word Length

**Claim.** For any four Boolean words and any one of their indices, the length of the word at that index is at most the maximum of the four word lengths.

**Proof.** The maximum is defined as the supremum of the four word lengths over all four indices. Every index belongs to this finite index set, so its corresponding length is at most that supremum, by the defining upper-bound property of a finite supremum.
