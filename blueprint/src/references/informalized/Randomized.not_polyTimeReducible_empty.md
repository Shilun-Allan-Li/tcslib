<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/Randomized/BPPEqP.lean :: Randomized.not_polyTimeReducible_empty -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# No Reduction to the Empty Language

**Claim.** There is no polynomial-time many-one reduction from the language of all finite binary strings to the empty language of binary strings.

**Proof.** Suppose such a reduction is witnessed by a function $f$. By the defining correctness condition for a many-one reduction, an input belongs to the source language if and only if its image under $f$ belongs to the target language. Apply this to the empty string: it belongs to the universal source language, so its image would have to belong to the empty target language, which is impossible.
