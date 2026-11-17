<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Programs/Light/Lib/Merge.lean :: Light.merge_meets -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Merge procedure correctness

**Claim.** Under the stated memory, separation, and word-bound hypotheses, the merge procedure executes within $40(|l|+|r|)+12$ steps, writes the sorted merge to the destination segment, and leaves all memory outside that segment unchanged.

**Proof.** Initialize the two progress counters to zero, then analyze the loop for $|l|+|r|$ rounds. The invariant `Taken` records that the counters $i,j$ count how many entries have been consumed from the two inputs, that the output written so far is the corresponding prefix of the sorted merge, and that all memory outside the destination segment is unchanged. Its initial case has $i=j=0$, empty output, and the original memory, so the invariant holds.

At a round with $i+j<|l|+|r|$, at least one input has an entry remaining. If both do, the segment assumptions identify the current memory reads with $l[i]$ and $r[j]$ (`Seg.get`). The procedure compares these entries: when $r[j]<l[i]$, the merge decomposition says the next output is $r[j]$ (`step_right`), and the right-taking body writes it and advances $j$ (`takeRight`). Otherwise $l[i]\le r[j]$, so the next output is $l[i]$ (`step_left`), and the left-taking body writes it and advances $i$ (`takeLeft`). If one input has ended, the corresponding end-case merge decomposition (`step_left_end` or `step_right_end`) shows that the next output comes from the other input, and the appropriate taking body preserves the invariant. The nested conditional branches follow the indicated comparison outcomes (`Stmt.Runs.ite_pos` and `Stmt.Runs.ite_neg`).

After $|l|+|r|$ rounds, both inputs have been consumed. The invariant's output is therefore the entire merge, and its memory condition gives preservation outside the destination segment. The loop bound follows from the round-cost estimate and is packaged with the invariant by `Ends.whileBlock`; the initial assignments and loop constitute the body execution, which yields the procedure guarantee via `Meets.of_body`.

**Key facts.** `Light.Meets.of_body`, `Light.Ends.whileBlock`, `Light.Merge.takeRight`, `Light.Merge.step_right`, `Light.Merge.takeLeft`, `Light.Merge.step_left`, `Light.Merge.step_left_end`, `Light.Merge.step_right_end`, `Light.Seg.get`, `Light.Stmt.Runs.ite_pos`, `Light.Stmt.Runs.ite_neg`.
