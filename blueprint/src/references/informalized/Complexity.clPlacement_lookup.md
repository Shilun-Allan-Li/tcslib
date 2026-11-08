<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CookLevin/Hardness.lean :: Complexity.clPlacement_lookup -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Lookup in an Injective Placement

**Claim.** For any host position, searching the ordered source slots for an index mapped to that position returns exactly the placement’s selection value.

**Proof.** Split according to whether the search returns an index. If it returns $i$, the defining property of the search says that the predicate holds at $i$, hence the embedding maps $i$ to the given position. The placement’s exactness condition then says that its selection at that position is $i$. If the search returns no index, split according to the selection value. A selection of none gives the desired equality immediately. If the selection were some $i$, exactness would imply that the embedding maps $i$ to the queried position; since $i$ occurs in the ordered list, the search could not have returned none. Thus that case is impossible.
