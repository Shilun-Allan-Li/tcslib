<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter04/HastadSwitching.lean :: FABL.CoordinateDecisionTree.wellFormed_queryCoordinates -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Well-Formedness of a Queried-Coordinate Tree

**Claim.** If $C$ is a list of distinct coordinates from $A$, and every finishing tree is well formed on the coordinates in $A$ outside $C$, then the tree that queries $C$ from a seed, with both bit branches at every query, is well formed with respect to $A$.

**Proof.** Induct on $C$, allowing the seed and available set to vary. If $C$ is empty, the queried tree is the finishing tree at the seed, which is well formed on all of $A$ by the hypothesis. Otherwise write $C=j::C'$. The distinctness and containment hypotheses give $j\in A$, as required for the root query. For either bit branch, apply the induction hypothesis to the tail in the available set with $j$ removed. The tail coordinates remain in that set: none equals $j$, by distinctness, and each belongs to $A$. Finally, the coordinates left after removing $j$ and then the tail are exactly the coordinates of $A$ outside the full list $j::C'$. Thus each finishing tree satisfies the induction hypothesis's required well-formedness condition, and both children are well formed after the root query.
