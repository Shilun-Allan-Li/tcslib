<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/Randomized/NPPoly.lean :: Randomized.flatMap_dup_map -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Duplicating elements under flat map

**Claim.** For any function $g$ and finite list $l$, concatenating two copies of $g(a)$ for each entry $a$ of $l$ gives the same list as first mapping $g$ over $l$ and then concatenating two copies of each resulting entry.

**Proof.** Induct on $l$. For the empty list, both sides are empty. If $l$ begins with $a$, flat-mapping its head contributes the two entries $g(a),g(a)$, followed by the flat-map over the tail. The induction hypothesis identifies the tail contributions with the flat-map of the mapped tail, so both lists have the same head pair and the same remainder.
