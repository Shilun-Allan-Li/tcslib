<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Programs/Util/List.lean :: List.toFinset_eq_image_of_length_eq_card -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# A list image equals a finite image

**Claim.** If $l$ is duplicate-free, its entries all lie in the image of $S$ under the injective map $g$, and its length equals the cardinality of $S$, then the set of entries of $l$ is exactly that image.

**Proof.** First, every entry of the list belongs to the image: the assumed representation of each entry as $g(x)$ for some $x\in S$ places it in $S$'s image under $g$. Thus the list's finite set of entries is contained in that image. The two finite sets have the same cardinality: injectivity makes the image have cardinality $|S|$, while absence of repetitions makes the list's set of entries have cardinality equal to the list length. The assumed length equality therefore gives equal cardinalities, and containment between finite sets of equal cardinality is equality.
