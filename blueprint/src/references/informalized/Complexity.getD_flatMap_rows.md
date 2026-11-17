<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/SpaceComplexity/Logspace/Path.lean :: Complexity.getD_flatMap_rows -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Indexing rows in a flat map

**Claim.** If each list $f(a)$ has length $k$, then for $i<|L|$ and $j<k$, the entry at index $ik+j$ of the flat map of $L$, with false as the default, equals the entry at index $j$ of $f(L_i)$ with the same default.

**Proof.** Induct on $L$, generalizing the row index $i$. If $L$ is empty, the condition $i<|L|$ cannot hold. For a nonempty list with head $a$ and tail $L'$, split on whether $i=0$. In that case, the relevant row is the head row $f(a)$, and its length $k$ together with $j<k$ ensures that appending the remaining flattened rows does not affect the indexed entry. If $i$ is a successor, the selected row lies in the tail. Its flattened index is shifted by the head block's length $k$: $(i+1)k+j=k+(ik+j)$. Removing that offset leaves exactly the tail index $ik+j$, so the induction hypothesis gives the claimed entry.
