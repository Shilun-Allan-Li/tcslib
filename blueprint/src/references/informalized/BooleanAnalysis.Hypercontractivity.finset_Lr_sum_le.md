<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/Hypercontractivity/Cube/Reverse/Tensorization.lean :: BooleanAnalysis.Hypercontractivity.finset_Lr_sum_le -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Minkowski Inequality for Finite Sums

**Claim.** For $r\ge1$ and a nonnegative array on finite index sets $s,t$, the $r$-norm over $t$ of the sum over $s$ is at most the sum over $s$ of the $r$-norms over $t$.

**Proof.** Proceed by induction on the finite set $s$. If $s$ is empty, both sides vanish. For the inductive step, write $s$ as the insertion of one index $i$ into a smaller set. For each $j\in t$, the sum over $s$ is the contribution $a(i,j)$ plus the sum over the smaller set. Minkowski's inequality for the finite $r$-norm, applicable because both summands are nonnegative and $r\ge1$, bounds the norm of this sum by the norm of the $i$th row plus the norm of the sum over the smaller set. The induction hypothesis bounds the latter by the sum of the remaining row norms. Adding the first row norm gives the required right-hand side.
