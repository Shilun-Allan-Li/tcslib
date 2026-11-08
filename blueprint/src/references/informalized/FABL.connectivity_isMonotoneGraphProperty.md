<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter08/GraphPropertyExamples.lean :: FABL.connectivity_isMonotoneGraphProperty -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Monotonicity of Connectivity

**Claim.** For every number of vertices, the property that an encoded graph is connected is monotone under adding edges.

**Proof.** Let $G$ and $H$ be encoded graphs with every edge of $G$ also present in $H$, and suppose $G$ is connected. Every adjacency in $G$ is then an adjacency in $H$, so each path witnessing that two vertices are connected in $G$ remains a path in $H$. Hence $H$ is connected, by the monotonicity of graph connectivity under edge inclusion (`EncodedGraphConnected.mono`).

**Key facts.** `FABL.EncodedGraphConnected.mono`.
