<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CookLevin/Snapshot.lean :: Complexity.prevVisit_none_no_visit -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# No previous visit implies distinct positions

**Claim.** If the last previous visit of tape $\tau$ at time $t$ is undefined, then at every time $r<t$ its head position differs from its position at time $t$.

**Proof.** An undefined maximum means the filtered list of earlier times whose head position equals the position at time $t$ is empty. If some $r<t$ had that same position, then $r$ would belong to the range of times below $t$ and satisfy the filter condition, putting it in the supposedly empty list. Hence no such $r$ exists.
