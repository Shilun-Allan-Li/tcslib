<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Programs/Light/Lib/Merge.lean :: Light.Merge.step_left -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Left Step in Merging

**Claim.** When both indexed entries exist and the entry from $l$ is at most the entry from $r$, merging the tails beginning at $i$ and $j$ yields the $i$th entry of $l$, followed by the merge of the tail of $l$ after that entry with the unchanged tail of $r$ beginning at $j$.

**Proof.** The index bounds let us write each tail as its indexed entry followed by the remaining tail: $l.drop\ i=l[i]::l.drop(i+1)$ and $r.drop\ j=r[j]::r.drop(j+1)$. The defining rule for merging two nonempty lists compares their heads; when the left head is at most the right head, it emits the left head and merges the left remainder with the entire right list. The hypothesis $l[i]\le r[j]$ selects this case, giving the stated equality.
