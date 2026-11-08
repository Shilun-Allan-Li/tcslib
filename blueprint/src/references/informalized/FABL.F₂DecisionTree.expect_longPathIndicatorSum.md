<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter03/SubspacesAndDecisionTrees/DecisionTreeFourier.lean :: FABL.F₂DecisionTree.expect_longPathIndicatorSum -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Expected Long-Path Indicator Sum

**Claim.** For a finite list of paths and a threshold $k$, the expected sum of the indicators of paths longer than $k$ equals the sum of their inverse sizes, with paths of length at most $k$ contributing zero.

**Proof.** Proceed by induction on the path list. The empty list contributes zero on both sides. For a list with first path $p$ and remaining list $P'$, the sum at each input is the first path's thresholded indicator plus the corresponding sum for $P'$. Linearity of expectation separates these contributions, and the induction hypothesis evaluates the tail. If $p$ is longer than $k$, its expected indicator is its inverse size, by the path-cylinder expectation formula (`expect_indicator`); if it is not longer, both its contribution and the claimed summand are zero. This gives the stated equality.

**Key facts.** `FABL.F₂DecisionTree.Path.expect_indicator`.
