<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/GraphTheory/Kruskal/Exchange.lean :: Kruskal.exchange_take_head' -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Reversed-Orientation Edge Exchange

**Claim.** If the stated endpoint connections hold, every pair connected using the list with $g$ at its head remains connected after appending $e$ to the list without $g$.

**Proof.** Replace $g$ by the edge with its endpoints reversed and the same weight. The hypotheses then give exactly the two endpoint connections required by the head-edge exchange result (Kruskal.exchange_take_head). For any adjacency using the original $g$, the reversed edge has the same undirected adjacency, since adjacency is symmetric in the endpoints. Consequently each such step is reachable in the target list; steps using other edges remain available there as well. Lifting this stepwise replacement to the whole path proves the result.

**Key facts.** `Kruskal.exchange_take_head`, `Kruskal.reach_lift`.
