<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter09/MatchingMomentCombinatorics.lean :: FABL.matching_eq_or_adj_of_toEdge_eq -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Matching Edge Equality Criterion

**Claim.** Let $G$ be a simple graph, let $M$ be a matching subgraph, and let $v,w$ be vertices of $M$. If the edges assigned to $v$ and $w$ by the matching are equal, then $v=w$ or $v$ and $w$ are adjacent in $M$.

**Proof.** Let $e$ be the edge assigned to $v$. The matching property ensures that $v$ is an endpoint of $e$; equality of the assigned edges ensures that $w$ is also an endpoint. Write the unordered pair of endpoints of $e$ as $\{u,z\}$. Each of $v$ and $w$ must then equal either $u$ or $z$. If they select the same endpoint, their underlying vertices agree, hence the vertices of the subgraph are equal. If they select opposite endpoints, the edge $e$ joins them, so they are adjacent in $M$. These possibilities prove the disjunction.
