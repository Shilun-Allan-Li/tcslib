<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Programs/Light/Lib/Merge.lean :: Light.Merge.step_right -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Right Step in Merging

**Claim.** When both indexed entries exist and the entry from $r$ is strictly less than the entry from $l$, merging the tails beginning at $i$ and $j$ yields the $j$th entry of $r$, followed by the merge of the unchanged tail of $l$ beginning at $i$ with the tail of $r$ after that entry.

**Proof.** The index bounds decompose the two tails into their heads and remainders: $l.drop\ i=l[i]::l.drop(i+1)$ and $r.drop\ j=r[j]::r.drop(j+1)$. The merge rule emits the left head when it is at most the right head, and otherwise emits the right head and merges the entire left list with the right remainder. Since $r[j]<l[i]$, the left head is not at most the right head, so the latter case gives the stated equality.
