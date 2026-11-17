<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter07/UniqueGamesReduction.lean :: FABL.FiniteUniqueGame.Walk.label_eq_transport -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Label Transport Along a Walk

**Claim.** If a labeling satisfies every constraint, then along any walk from $u$ to $v$, the label at $v$ is obtained by transporting the label at $u$ along that walk.

**Proof.** Proceed by induction on the walk. For the empty walk, the endpoints agree and transport leaves the label unchanged. For a forward edge $e$, satisfaction says that the permutation sends the target label to the source label. Applying its inverse shows that the target label is the inverse-permutation image of the source label, exactly the forward transport. For a backward traversal of $e$, the same satisfaction equation directly says that the source label is the permutation image of the target label, as required by backward transport. Finally, for a walk formed by concatenating a first walk and a second walk, apply the induction statement to the first part and then the second: the intermediate label is transported first along the first part and then along the second, which is the definition of transport along the concatenation.
