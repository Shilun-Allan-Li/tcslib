<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter03/GoldreichLevin/Controller.lean :: FABL.goldreichLevinCandidates_subset_prefixCoordinates_succ -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Candidate sets extend the prefix

**Claim.** If each active set lies among the first $k$ coordinates, then every candidate formed from an active set by either keeping it or adjoining coordinate $k+1$ lies among the first $k+1$ coordinates.

**Proof.** Take a candidate $T$. The membership characterization of the candidate family says that there is an active set $S$ such that either $T=S$ or $T=S\cup\{k+1\}$ (`mem_goldreichLevinCandidates_iff`). By hypothesis, $S$ is contained in the first $k$ coordinates. The first $k+1$ coordinates consist of the first $k$ coordinates together with coordinate $k+1$ (`prefixCoordinates_succ`). If $T=S$, it is therefore contained in the enlarged prefix. If $T$ is obtained by adjoining coordinate $k+1$, both its old elements and the added coordinate lie in that prefix, so the same containment follows.

**Key facts.** `FABL.mem_goldreichLevinCandidates_iff`, `FABL.prefixCoordinates_succ`.
