<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/SpaceComplexity/ExpBFS/Relax.lean :: Complexity.LogProg.ExpBFS.out_update -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Memory Update Outside the Marked Region

**Claim.** If $v<K$, updating memory at cell $b+v$ to true leaves unchanged every cell other than $b+u$ for $u<K$.

**Proof.** Fix a cell $z$ outside the marked region, so $z\ne b+u$ for every $u<K$. Since $v<K$, this applies in particular to $u=v$, and hence $z\ne b+v$. A function update agrees with the original function at every argument distinct from the updated argument. Therefore the updated memory at $z$ equals the original memory at $z$.
