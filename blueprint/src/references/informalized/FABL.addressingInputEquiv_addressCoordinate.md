<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter09/FriedgutNecessity.lean :: FABL.addressingInputEquiv_addressCoordinate -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Address coordinates under decomposition

**Claim.** For every $m$, input $x$, and address index $i<m$, the $i$th coordinate of the address part in the decomposition of $x$ equals the coordinate of $x$ at address position $i$.

**Proof.** The decomposition reindexes the input coordinates using the equivalence between the disjoint union of address and data positions and the full coordinate set. Evaluating its address component at $i$ therefore reads the original input at the position corresponding to the left summand indexed by $i$, which is precisely the address coordinate of $x$.
