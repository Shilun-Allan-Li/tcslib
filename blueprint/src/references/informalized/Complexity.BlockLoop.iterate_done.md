<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/ClassNP/PolyTimeBlockLoop.lean :: Complexity.BlockLoop.iterate_done -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Orbit Reaches the Completed State

**Claim.** For a step map determined by update and next-state maps, if $p$ is nonempty and the $K$th iterate from $s_0$ encodes $p$ together with the empty string and $q$, then every iterate with index $i>K$ is the completed-block string.

**Proof.** Write $i=j+(K+1)$, which is possible because $K<i$. The iterate-addition law reduces the claim to showing that the $(K+1)$st iterate reaches the completed state and that this state remains fixed. The hypothesis at time $K$ identifies the state as the encoding of $p$ and an inner encoding whose first component is empty. One more application of the step map therefore enters its completed-state branch (using that $p$ is nonempty), so the $(K+1)$st iterate is $blockDone$. Induct on $j$: the base case is this fact, and each successor case follows by applying the fixed-point property of the completed state ($step_done$).

**Key facts.** `Complexity.BlockLoop.step_done`.
