<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/SpaceComplexity/Machines/ARMProof.lean :: Complexity.LogProg.length_vword_le -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Upper bound for virtual word length

**Claim.** For every finite list of segments, the virtual word's length is at most the sum of their rendered lengths plus twice the number of segments.

**Proof.** Induct on the segment list. For the empty list, both the virtual word and the sum are empty, so the bound holds. For a singleton, the virtual word is just its rendering, and its length is at most its rendered length plus two. For a list with at least two elements, its virtual word consists of the first rendered segment, a two-bit separator, and the virtual word of the tail. By the induction hypothesis, the tail length is bounded by the sum of its rendered lengths plus twice its number of segments. Adding the first segment and separator gives a bound no greater than the sum of rendered lengths for the full list plus twice its length; the remaining arithmetic is the corresponding natural-number inequality.

**Key facts.** `Complexity.LogProg.length_render`.
