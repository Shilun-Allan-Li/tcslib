<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Programs/Light/Lib/Merge.lean :: Light.Merge.step_right_end -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Right Step When the Left Tail Ends

**Claim.** If $|l|\le i$ and $j<|r|$, merging the tails beginning at $i$ and $j$ yields the $j$th entry of $r$, followed by the merge of the unchanged tail of $l$ beginning at $i$ with the tail of $r$ beginning at $j+1$.

**Proof.** Since $i$ is at least the length of $l$, the tail $l.drop\ i$ is empty. Merging the empty list with another list returns that other list, so the left side reduces to $r.drop\ j$. The bound $j<|r|$ writes this tail as $r[j]$ followed by $r.drop(j+1)$. On the right, merging the empty left tail with $r.drop(j+1)$ leaves that tail unchanged, giving the same list.
