<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Programs/Light/Lib/Seg.lean :: Light.vecAt_of_seg -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Vector values from a list segment

**Claim.** If the segment of memory beginning at $a$ is the list whose $k$th entry is the integer represented by $I(k)$, then for every $k<t$, the memory value at $a+k$ equals the integer represented by $I(k)$.

**Proof.** Fix $k$ in the finite index set. By the segment hypothesis, the memory value at $a+k$ equals the entry at position $k$ in the specified list. Since $k<t$, this position is within the list. By the definition of the list constructed from the function $I$, its entry at position $k$ is the integer represented by $I(k)$.
