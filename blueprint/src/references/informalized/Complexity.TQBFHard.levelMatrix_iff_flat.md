<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/ClassPSPACE/TQBFHardSemantics.lean :: Complexity.TQBFHard.levelMatrix_iff_flat -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Flattened characterization of the level matrix

**Claim.** The recursive level-matrix condition at the specified position holds exactly when some selector condition fails during the first $r$ levels, or the endpoint pair at level $r$ satisfies $E$.

**Proof.** Induct on the number of levels $r$, proving the equivalence for every starting index $j$. At depth zero, the recursive condition is just $E(u_j,v_j)$, and there are no indices witnessing a selector failure, so the claim follows. For the successor step, the recursive definition first requires the selector condition at level $j$, then applies the depth-$r$ condition starting at $j+1$. The arithmetic identity for the starting position makes this precisely the induction hypothesis at that next index. If the first selector condition fails, it itself supplies a failure witness at index zero. If it holds, the induction hypothesis says either a later selector condition fails or the final pair satisfies $E$; shifting each later witness index down by one gives a witness among the successor statement's first $r+1$ levels. Conversely, a failure witness at index zero contradicts the initial selector requirement. Any witness with positive index shifts down to a later-level witness for the induction hypothesis, while the endpoint alternative passes directly through that hypothesis. The index shifts and endpoint reindexing are natural-number equalities.
