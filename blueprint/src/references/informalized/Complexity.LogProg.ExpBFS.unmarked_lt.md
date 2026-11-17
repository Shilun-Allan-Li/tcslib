<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/SpaceComplexity/ExpBFS/Search.lean :: Complexity.LogProg.ExpBFS.unmarked_lt -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Strict Decrease in Unmarked Count

**Claim.** If $M$ is pointwise contained in $M'$, the markings agree outside the specified finite range, and $M'\ne M$, then the range contains strictly fewer unmarked cells under $M'$ than under $M$.

**Proof.** Since the markings differ, choose a cell $z$ where they differ. Agreement outside the specified range forces $z=b+v$ for some $v<K$. At this cell, monotonicity and the fact that the markings differ imply $M(z)=\mathrm{false}$ and $M'(z)=\mathrm{true}$. Every index in the range that is unmarked under $M'$ is also unmarked under $M$: if it were marked under $M$, monotonicity would make it marked under $M'$. Thus the set counted by the unmarked count for $M'$ is contained in the corresponding set for $M$. The index $v$ belongs to the latter set but not the former, so this containment is strict. The cardinality of a strict subset of a finite set is strictly smaller, proving the claim.
