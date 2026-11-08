<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Build/Seam.lean :: Turing.seamCompTM_visitedByTapeHead -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Visited Cells Under Seam Composition

**Claim.** The cells visited by each work-tape head in the seam-composed run through time $T_1+1+T_2$ are contained in the union of the cells visited in the two component runs.

**Proof.** Apply the general visited-cell inclusion result (`seamComp_visited_general`) to the first run, its exit-state condition, and the fact that it avoids the exit state before time $T_1$. This gives the inclusion for arbitrary configurations. The initial configurations here are word configurations, so their state embeddings identify with the corresponding word configurations (`seam_ofWords_mapState`); substituting these identifications yields the stated inclusion.

**Key facts.** `Turing.seamComp_visited_general`, `Turing.seam_ofWords_mapState`.
