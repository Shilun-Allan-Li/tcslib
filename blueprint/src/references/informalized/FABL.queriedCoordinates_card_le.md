<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter07/PCPPConstructions.lean :: FABL.queriedCoordinates_card_le -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Queried-Coordinate Bound

**Claim.** For each seed of a nonadaptive tester making $r$ query slots on strings of length $n$, the number of distinct queried coordinates is at most $r$.

**Proof.** For every queried coordinate, choose one query slot that addresses it. This choice maps the finite set of queried coordinates into the $r$ slots. The map is injective: if two coordinates were assigned the same slot, that slot’s query would equal both coordinates, so the coordinates would be equal. Hence the number of queried coordinates is at most the number of slots, namely $r$.
