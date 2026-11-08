<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/Randomized/RandomWalkHitting.lean :: Randomized.RegularMultigraph.avg_const -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Average of a constant function

**Claim.** For a finite regular multigraph of positive degree, the average of a constant rational-valued function over the neighbors of any vertex equals that constant.

**Proof.** At a vertex $s$, every one of the $D$ neighbor slots contributes the same value $c$, so their sum is $Dc$. The average divides this sum by $D$, which is nonzero because the degree is positive; hence the result is $c$.
