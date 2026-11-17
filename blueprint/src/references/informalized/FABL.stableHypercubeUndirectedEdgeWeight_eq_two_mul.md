<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter09/SmallSetExpansion.lean :: FABL.stableHypercubeUndirectedEdgeWeight_eq_two_mul -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Undirected Edge Weight Identity

**Claim.** For $-1\leq\rho\leq1$ and cube points $x,y$, the undirected stable hypercube edge weight from $x$ to $y$ equals twice the directed stable edge weight from $x$ to $y$.

**Proof.** By definition, the undirected weight is the sum of the directed weights from $x$ to $y$ and from $y$ to $x$. The directed edge weight is symmetric in its endpoints (`stableHypercubeEdgeWeight_comm`), so these two terms are equal. Their sum is therefore twice either term.

**Key facts.** `FABL.stableHypercubeEdgeWeight_comm`.
