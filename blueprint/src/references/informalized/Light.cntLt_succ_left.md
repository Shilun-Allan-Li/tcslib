<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Programs/Util/CountingSort.lean :: Light.cntLt_succ_left -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Counting at a Successor Threshold

**Claim.** The number of indices below $j$ with $kf(i)<t+1$ equals the number with $kf(i)<t$ plus the number with $kf(i)=t$.

**Proof.** Induct on $j$. At $j=0$, all three counts vanish. For the successor step, the count-successor formula (`Light.cntLt_succ_right`) expands each threshold count by its contribution at the new index $j$, and the equality-count successor formula (`Light.cntEq_succ`) does the same for the equality count. Using the induction hypothesis reduces the desired identity to checking the contributions at $j$: for natural numbers, $kf(j)<t+1$ holds exactly when either $kf(j)<t$ or $kf(j)=t$, and these alternatives are disjoint. Their indicator contributions therefore satisfy the required addition identity.

**Key facts.** `Light.cntLt_succ_right`, `Light.cntEq_succ`.
