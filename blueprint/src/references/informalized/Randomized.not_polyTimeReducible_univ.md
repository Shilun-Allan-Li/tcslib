<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/Randomized/BPPEqP.lean :: Randomized.not_polyTimeReducible_univ -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# No Reduction from the Empty Language

**Claim.** There is no polynomial-time many-one reduction from the empty language of binary strings to the language of all finite binary strings.

**Proof.** Suppose such a reduction is witnessed by a function $f$. Its correctness condition says that an input belongs to the empty source language if and only if its image belongs to the universal target language. For the empty string, the latter membership holds because every finite binary string belongs to the target. The equivalence would therefore put the empty string in the empty source language, a contradiction.
