<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter07/PCPPConstructions.lean :: FABL.exists_unqueried_coordinate -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# An unqueried coordinate

**Claim.** If a tester makes $r<n$ nonadaptive queries for a fixed seed, there is a coordinate that none of its query positions asks for.

**Proof.** For the fixed seed, the set of queried coordinates has cardinality at most $r$ (`queriedCoordinates_card_le`), hence strictly less than $n$. It is therefore a proper subset of the $n$ coordinates, so choose a coordinate $i$ outside it. If any query position asked for $i$, the definition of the queried-coordinate set would put $i$ in that set, contradicting its choice. Thus every query position avoids $i.

**Key facts.** `FABL.queriedCoordinates_card_le`.
