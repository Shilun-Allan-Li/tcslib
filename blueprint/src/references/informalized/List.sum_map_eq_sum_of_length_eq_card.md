<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Programs/Util/List.lean :: List.sum_map_eq_sum_of_length_eq_card -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Sum over an Injective Finite Image

**Claim.** If a repetition-free list lies in the image of an injective map from a finite set and its length equals that set's cardinality, then its mapped sum equals the sum over the finite set of the corresponding image values.

**Proof.** First replace the list sum by the sum over its underlying finite set; this is valid because the list has no repetitions. The image of $S$ under $g$ contains every element of the list by the subset hypothesis. Injectivity makes the image have cardinality $|S|$, while the list's underlying set has cardinality equal to the list length, also $|S|$. Thus the containment is equality: `List.toFinset_eq_image_of_length_eq_card` supplies this finite-set identification. The sum is now over the image of $S$. Reindexing an injective image sum gives the sum over $S$, since distinct elements of $S$ have distinct images.

**Key facts.** `List.toFinset_eq_image_of_length_eq_card`.
