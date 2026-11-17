<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Programs/Light/Lib/Merge.lean :: Light.Merge.step_left_end -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Left Step When the Right Tail Ends

**Claim.** If $i<|l|$ and $|r|\le j$, merging the tails beginning at $i$ and $j$ yields the $i$th entry of $l$, followed by the merge of the tail of $l$ beginning at $i+1$ with the same tail of $r$.

**Proof.** Because $j$ is at least the length of $r$, the tail $r.drop\ j$ is empty. Merging any list with the empty list returns that list, so the left side reduces to $l.drop\ i$. Since $i<|l|$, this tail is $l[i]$ followed by $l.drop(i+1)$. On the right, the merge with the empty tail likewise leaves $l.drop(i+1)$ unchanged, yielding the same list.
