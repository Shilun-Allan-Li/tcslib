<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter09/FriedgutNecessity.lean :: FABL.addressingInputEquiv_dataCoordinate -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Data coordinates under decomposition

**Claim.** For every $m$, input $x$, and data index $j<2^m$, the $j$th coordinate of the data part in the decomposition of $x$ equals the coordinate of $x$ at data position $j$.

**Proof.** The decomposition reindexes the input coordinates by the equivalence between the disjoint union of address and data positions and the full coordinate set. Evaluating its data component at $j$ reads the original input at the position corresponding to the right summand indexed by $j$, namely the data coordinate of $x$ at position $j$.
